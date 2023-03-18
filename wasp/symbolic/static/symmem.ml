type size = int32
type address = int64
type offset = int32

module type MemoryBackend = sig
  type t

  exception Bounds

  val store_byte : t -> address -> Symvalue.sym_expr -> unit

  val load_byte : t -> address -> Symvalue.sym_expr

  val from_heap : Heap.t -> t

  val clone : t -> t * t

  val to_string : t -> string
end

module LazyMemory : MemoryBackend = struct
  type t = {
    map: (address, Symvalue.sym_expr) Hashtbl.t;
    parent : t Option.t;
  }

  exception Bounds

  let store_byte
      (lmem : t)
      (a : address)
      (b : Symvalue.sym_expr)
      : unit =
    Hashtbl.replace lmem.map a b

  let load_byte
      (lmem : t)
      (a : address)
      : Symvalue.sym_expr =
    let rec load_byte_rec
        (lmem : t)
        : Symvalue.sym_expr Option.t =
      match Hashtbl.find_opt lmem.map a with
      | Some b -> Some b
      | None -> Option.bind lmem.parent (fun p -> load_byte_rec p)
    in

    match Hashtbl.find_opt lmem.map a with
    | Some b -> b
    | None -> begin match Option.bind lmem.parent load_byte_rec with
      | Some b -> begin
        Hashtbl.add lmem.map a b;
        b
      end
      | None -> Symvalue.Extract (Symvalue.Value (Values.I64 0L), 1, 0)
    end

  let from_heap (heap : Heap.t) : t =
    let concolic_seq = (Heap.to_seq heap) in
    let concolic_to_symbolic (k, (_, s)) = (k, s) in
    {
      map = Hashtbl.of_seq (Seq.map concolic_to_symbolic concolic_seq);
      parent = None
    }

  let clone (lmem : t) : t * t =
    let child1 = {
      map = Hashtbl.create Flags.hashtbl_default_size;
      parent = Some lmem;
    }
    in
    let child2 = {
      map = Hashtbl.create Flags.hashtbl_default_size;
      parent = Some lmem;
    }
    in
    child1, child2

  let to_string (lmem : t) : string =
    (* TODO: need to go all the way up the chain *)
    let lst = List.sort (fun (a, _) (b, _) -> compare a b) (List.of_seq (Hashtbl.to_seq lmem.map)) in
    List.fold_right (
      fun (a, se) acc ->
        "(" ^ (Int64.to_string a) ^ "->" ^
        "(" ^ (Symvalue.to_string se) ^ ")" ^
        ")\n" ^ acc
    ) lst ""
end

module MapMemory : MemoryBackend = struct
  type t = (address, Symvalue.sym_expr) Hashtbl.t

  let store_byte
      (map : t)
      (a : address)
      (b : Symvalue.sym_expr) =
    Hashtbl.replace map a b

  let load_byte
      (map : t)
      (a : address)
      : Symvalue.sym_expr =
    match Hashtbl.find_opt map a with
    | Some b -> b
    | None -> Symvalue.Extract (Symvalue.Value (Values.I64 0L), 1, 0)

  let from_heap (map : Heap.t) : t =
    let concolic_seq = (Heap.to_seq map) in
    let concolic_to_symbolic (k, (_, s)) = (k, s) in
    Hashtbl.of_seq (Seq.map concolic_to_symbolic concolic_seq)

  let clone (map : t) : t * t =
    map, Hashtbl.copy map

  let to_string (map : t) : string =
    let lst = List.sort (fun (a, _) (b, _) -> compare a b) (List.of_seq (Hashtbl.to_seq map)) in
    List.fold_right (
      fun (a, se) acc ->
        "(" ^ (Int64.to_string a) ^ "->" ^
        "(" ^ (Symvalue.to_string se) ^ ")" ^
        ")\n" ^ acc
    ) lst ""

  exception Bounds

end

module TreeMemory : MemoryBackend = struct
  module Int64Map = Map.Make(Int64)

  type t = { mutable tree: Symvalue.sym_expr Int64Map.t }

  let store_byte
      (map : t)
      (a : address)
      (b : Symvalue.sym_expr) =
    map.tree <- Int64Map.add a b map.tree

  let load_byte
      (map : t)
      (a : address)
      : Symvalue.sym_expr =
    match Int64Map.find_opt a map.tree with
    | Some b -> b
    | None -> Symvalue.Extract (Symvalue.Value (Values.I64 0L), 1, 0)

  let from_heap (map : Heap.t) : t =
    let concolic_seq = (Heap.to_seq map) in
    let concolic_to_symbolic (k, (_, s)) = (k, s) in
    { tree = Int64Map.of_seq (Seq.map concolic_to_symbolic concolic_seq)}

  let clone (map : t) : t * t =
    map, {tree = map.tree}

  let to_string (map : t) : string =
    let lst = (List.of_seq (Int64Map.to_seq map.tree)) in
    List.fold_right (
      fun (a, se) acc ->
        "(" ^ (Int64.to_string a) ^ "->" ^
        "(" ^ (Symvalue.to_string se) ^ ")" ^
        ")\n" ^ acc
    ) lst ""

  exception Bounds
end

module type SymbolicMemory = sig
  type t

  exception Bounds

  val from_heap : Heap.t -> t

  val clone : t -> t * t

  val load_value : t -> address -> offset -> Types.value_type ->
    Symvalue.sym_expr

  val load_packed : Memory.pack_size -> t -> address -> offset
      ->Types.value_type -> Symvalue.sym_expr

  val load_string : t -> address -> string

  val store_value : t -> address -> offset -> Symvalue.sym_expr -> unit

  val store_packed : Memory.pack_size -> t -> address -> offset -> Symvalue.sym_expr -> unit

  val to_string : t -> string

end

module SMem (MB : MemoryBackend) : SymbolicMemory = struct
  type t = MB.t

  exception Bounds = MB.Bounds

  (* helper functions *)
  let effective_address (a : address) (o : offset) : address =
    let ea = Int64.(add a (of_int32 o)) in
    if I64.lt_u ea a then raise MB.Bounds;
    ea

  let length_pack_size (sz : Memory.pack_size) : int =
    match sz with
    | Memory.Pack8 -> 1
    | Memory.Pack16 -> 2
    | Memory.Pack32 -> 4

  let storen
      (mem : MB.t)
      (a : address)
      (o : offset)
      (n : int)
      (value : Symvalue.sym_expr)
      : unit =
    let rec loop mem a i n x =
      if n > i then begin
        MB.store_byte mem a (Symvalue.Extract (x, i+1, i));
        loop mem (Int64.add a 1L) (i + 1) n x;
      end
    in loop mem (effective_address a o) 0 n value

  let loadn
      (mem : MB.t)
      (a : address)
      (o : offset)
      (n : int)
      : Symvalue.sym_expr list =
    let rec loop a n acc =
      if n = 0 then acc else begin
        let se = MB.load_byte mem a in
        loop (Int64.sub a 1L) (n - 1) (se :: acc)
      end
    in loop Int64.(add (effective_address a o) (of_int (n - 1))) n []

  (* Public functions *)
  let from_heap = MB.from_heap

  let clone = MB.clone

  let load_value
      (mem : MB.t)
      (a : address)
      (o : offset)
      (ty : Types.value_type) :
      Symvalue.sym_expr =
    let exprs = loadn mem a o (Types.size ty) in
    let expr = List.(
      fold_left (fun acc e -> Symvalue.Concat (e, acc))
      (hd exprs)
      (tl exprs)
    )
    in
    (* simplify concats *)
    let expr = Symvalue.simplify expr in
    (* remove extract *)
    let expr = Symvalue.simplify ~extract:true expr in
    let open Values in
    let expr =
    match ty with
      | Types.I32Type -> begin
        match expr with
        | Symvalue.Value (I64 v) -> Symvalue.Value (I32 (Int64.to_int32 v))
        | _ -> expr
      end
      | Types.I64Type -> expr
      | Types.F32Type -> begin
        match expr with
        | Symvalue.Value (I64 v) -> Symvalue.Value (F32 (F32.of_bits (Int64.to_int32 v)))
        | Symvalue.I32Cvtop (Si32.I32ReinterpretFloat, v) -> v
        | _ -> Symvalue.F32Cvtop (Sf32.F32ReinterpretInt, expr)
      end
      | Types.F64Type -> begin
        match expr with
        | Symvalue.Value (I64 v) -> Symvalue.Value (F64 (F64.of_bits v))
        | Symvalue.I64Cvtop (Si64.I64ReinterpretFloat, v) -> v
        | _ -> Symvalue.F64Cvtop (Sf64.F64ReinterpretInt, expr)
      end
    in
    expr

  let load_packed
      (sz : Memory.pack_size)
      (mem : MB.t)
      (a : address)
      (o : offset)
      (ty : Types.value_type) :
      Symvalue.sym_expr =
    let exprs = loadn mem a o (length_pack_size sz) in
    let open Values in
    (* pad with 0s *)
    let expr =
      let rec loop acc i =
        if i >= (Types.size ty) then acc
        else loop (acc @ [Symvalue.Extract (Symvalue.Value (I64 0L), 1, 0)]) (i + 1) in
      let exprs = loop exprs (List.length exprs) in
      List.(
        fold_left (fun acc e -> Symvalue.Concat (e, acc)) (hd exprs) (tl exprs)
    )
    in
    (* simplify concats *)
    let expr = Symvalue.simplify expr in
    (* remove extract *)
    let expr = Symvalue.simplify ~extract:true expr in
    let expr =
    match ty with
      | Types.I32Type -> begin
        match expr with
        | Symvalue.Value (I64 v) -> Symvalue.Value (I32 (Int64.to_int32 v))
        | _ -> expr
      end
      | Types.I64Type -> expr
      | _ -> failwith "load_packed only exists for i32 and i64"
    in
    expr

  let load_string (mem : MB.t) (a : address) : string =
    let rec loop a acc =
      let sb = MB.load_byte mem a in
      let b =
        match sb with
        | Symvalue.Extract (Symvalue.Value (Values.I64 b), 1, 0) ->
            Int64.to_int b
        | _ -> failwith ("Symmem.load_string failed to load a char" ^
        "\nThe value loaded was: " ^ (Symvalue.to_string sb))
      in
      if b = 0 then
        acc
      else
        loop (Int64.add a 1L) (acc ^ Char.(escaped (chr b)))
    in
    loop a ""

  let store_value
      (mem : MB.t)
      (a : address)
      (o : offset)
      (value : Symvalue.sym_expr)
      : unit =
    let ty = Symvalue.type_of value in
    let sz = Types.size ty in
    let open Values in
    let value =
    match ty with
    | Types.I32Type -> begin
      match value with
      | Symvalue.Value (I32 i) -> Symvalue.Value (I64 (Int64.of_int32 i))
      | _ -> value
    end
    | Types.I64Type -> value
    | Types.F32Type -> begin match value with
      | Symvalue.Value (F32 f) -> Symvalue.Value (I64 (Int64.of_int32 (F32.to_bits f)))
      | _ -> Symvalue.I32Cvtop (Si32.I32ReinterpretFloat, value)
    end
    | Types.F64Type -> begin match value with
      | Symvalue.Value (F64 f) -> Symvalue.Value (I64 (F64.to_bits f))
      | _ -> Symvalue.I64Cvtop (Si64.I64ReinterpretFloat, value)
    end
    in
    storen mem a o sz value

  let store_packed
      (sz : Memory.pack_size)
      (mem : MB.t)
      (a : address)
      (o : offset)
      (value : Symvalue.sym_expr) =
    let value : Symvalue.sym_expr =
      match value with
      | Symvalue.Value (Values.I32 x) -> Symvalue.Value (Values.I64 (Int64.of_int32 x))
      | Symvalue.Value (Values.I64 x) -> Symvalue.Value (Values.I64 x)
      | _ -> value
    in
    storen mem a o (length_pack_size sz) value

  let to_string = MB.to_string

end

module LazySMem : SymbolicMemory = SMem(LazyMemory)
module MapSMem : SymbolicMemory = SMem(MapMemory)
module TreeSMem : SymbolicMemory = SMem(TreeMemory)
