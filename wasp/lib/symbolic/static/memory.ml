open Encoding
open Expression
open Types
open Interpreter.Memory

type size = int32
type address = int64
type offset = int32

module type MemoryBackend = sig
  type t

  exception Bounds

  val store_byte : t -> address -> Expression.t -> unit

  val load_byte : t -> address -> Expression.t

  val from_heap : Concolic.Heap.t -> t

  val clone : t -> t * t

  val to_string : t -> string
end

module LazyMemory : MemoryBackend = struct
  type t = {
    map: (address, Expression.t) Hashtbl.t;
    parent : t Option.t;
  }

  exception Bounds

  let store_byte
      (lmem : t)
      (a : address)
      (b : Expression.t)
      : unit =
    Hashtbl.replace lmem.map a b

  let load_byte
      (lmem : t)
      (a : address)
      : Expression.t =
    let rec load_byte_rec
        (lmem : t)
        : Expression.t Option.t =
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
      | None -> Extract (Num (I64 0L), 1, 0)
    end

  let from_heap (heap : Concolic.Heap.t) : t =
    let concolic_seq = (Concolic.Heap.to_seq heap) in
    let concolic_to_symbolic (k, (_, s)) = (k, s) in
    {
      map = Hashtbl.of_seq (Seq.map concolic_to_symbolic concolic_seq);
      parent = None
    }

  let clone (lmem : t) : t * t =
    let child1 = {
      map = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
      parent = Some lmem;
    }
    in
    let child2 = {
      map = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
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
        "(" ^ (Expression.to_string se) ^ ")" ^
        ")\n" ^ acc
    ) lst ""
end

module MapMemory : MemoryBackend = struct
  type t = (address, Expression.t) Hashtbl.t

  let store_byte
      (map : t)
      (a : address)
      (b : Expression.t) =
    Hashtbl.replace map a b

  let load_byte
      (map : t)
      (a : address)
      : Expression.t =
    match Hashtbl.find_opt map a with
    | Some b -> b
    | None -> Extract (Num (I64 0L), 1, 0)

  let from_heap (map : Concolic.Heap.t) : t =
    let concolic_seq = (Concolic.Heap.to_seq map) in
    let concolic_to_symbolic (k, (_, s)) = (k, s) in
    Hashtbl.of_seq (Seq.map concolic_to_symbolic concolic_seq)

  let clone (map : t) : t * t =
    map, Hashtbl.copy map

  let to_string (map : t) : string =
    let lst = List.sort (fun (a, _) (b, _) -> compare a b) (List.of_seq (Hashtbl.to_seq map)) in
    List.fold_right (
      fun (a, se) acc ->
        "(" ^ (Int64.to_string a) ^ "->" ^
        "(" ^ (Expression.to_string se) ^ ")" ^
        ")\n" ^ acc
    ) lst ""

  exception Bounds

end

module TreeMemory : MemoryBackend = struct
  module Int64Map = Map.Make(Int64)

  type t = { mutable tree: Expression.t Int64Map.t }

  let store_byte
      (map : t)
      (a : address)
      (b : Expression.t) =
    map.tree <- Int64Map.add a b map.tree

  let load_byte
      (map : t)
      (a : address)
      : Expression.t =
    match Int64Map.find_opt a map.tree with
    | Some b -> b
    | None -> Extract (Num (I64 0L), 1, 0)

  let from_heap (map : Concolic.Heap.t) : t =
    let concolic_seq = (Concolic.Heap.to_seq map) in
    let concolic_to_symbolic (k, (_, s)) = (k, s) in
    { tree = Int64Map.of_seq (Seq.map concolic_to_symbolic concolic_seq)}

  let clone (map : t) : t * t =
    map, {tree = map.tree}

  let to_string (map : t) : string =
    let lst = (List.of_seq (Int64Map.to_seq map.tree)) in
    List.fold_right (
      fun (a, se) acc ->
        "(" ^ (Int64.to_string a) ^ "->" ^
        "(" ^ (Expression.to_string se) ^ ")" ^
        ")\n" ^ acc
    ) lst ""

  exception Bounds
end

module type SymbolicMemory = sig
  type t

  exception Bounds

  val from_heap : Concolic.Heap.t -> t

  val clone : t -> t * t

  val load_value : t -> address -> offset -> num_type -> Expression.t

  val load_packed : pack_size -> t -> address -> offset
      -> num_type -> Expression.t

  val load_string : t -> address -> string

  val store_value : t -> address -> offset -> Expression.t -> unit

  val store_packed : pack_size -> t -> address -> offset -> Expression.t -> unit

  val to_string : t -> string

end

module SMem (MB : MemoryBackend) : SymbolicMemory = struct
  type t = MB.t

  exception Bounds = MB.Bounds

  (* helper functions *)
  let effective_address (a : address) (o : offset) : address =
    let ea = Int64.(add a (of_int32 o)) in
    if Interpreter.I64.lt_u ea a then raise MB.Bounds;
    ea

  let length_pack_size (sz : pack_size) : int =
    match sz with
    | Pack8 -> 1
    | Pack16 -> 2
    | Pack32 -> 4

  let storen
      (mem : MB.t)
      (a : address)
      (o : offset)
      (n : int)
      (value : Expression.t)
      : unit =
    let rec loop mem a i n x =
      if n > i then begin
        MB.store_byte mem a (Expression.Extract (x, i+1, i));
        loop mem (Int64.add a 1L) (i + 1) n x;
      end
    in loop mem (effective_address a o) 0 n value

  let loadn
      (mem : MB.t)
      (a : address)
      (o : offset)
      (n : int)
      : Expression.t list =
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
      (ty : num_type) :
      Expression.t =
    let exprs = loadn mem a o (Types.size ty) in
    let expr = List.(
      fold_left (fun acc e -> Expression.Concat (e, acc))
      (hd exprs)
      (tl exprs)
    )
    in
    (* simplify concats *)
    let expr = Expression.simplify expr in
    (* remove extract *)
    let expr = Expression.simplify ~extract:true expr in
    let expr =
    match ty with
      | Types.I32Type -> begin
        match expr with
        | Num (I64 v) -> Num (I32 (Int64.to_int32 v))
        | _ -> expr
      end
      | Types.I64Type -> expr
      | Types.F32Type -> begin
        match expr with
        | Num (I64 v) -> Num (F32 (Int32.bits_of_float (Int64.float_of_bits v)))
        | Cvtop (I32 I32.ReinterpretFloat, v) -> v
        | _ -> Cvtop (F32 F32.ReinterpretInt, expr)
      end
      | Types.F64Type -> begin
        match expr with
        | Num (I64 v) -> Num (F64 v)
        | Cvtop (I64 I64.ReinterpretFloat, v) -> v
        | _ -> Cvtop (F64 F64.ReinterpretInt, expr)
      end
    in
    expr

  let load_packed
      (sz : pack_size)
      (mem : MB.t)
      (a : address)
      (o : offset)
      (ty : num_type) :
      Expression.t =
    let exprs = loadn mem a o (length_pack_size sz) in
    (* pad with 0s *)
    let expr =
      let rec loop acc i =
        if i >= (Types.size ty) then acc
        else loop (acc @ [Extract (Num (I64 0L), 1, 0)]) (i + 1) in
      let exprs = loop exprs (List.length exprs) in
      List.(fold_left (fun acc e -> e ++ acc) (hd exprs) (tl exprs))
    in
    (* simplify concats *)
    let expr = Expression.simplify expr in
    (* remove extract *)
    let expr = Expression.simplify ~extract:true expr in
    let expr =
    match ty with
      | Types.I32Type -> begin
        match expr with
        | Num (I64 v) -> Num (I32 (Int64.to_int32 v))
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
        | Extract (Num (I64 b), 1, 0) -> Int64.to_int b
        | _ -> failwith ("Symmem.load_string failed to load a char" ^
        "\nThe value loaded was: " ^ (Expression.to_string sb))
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
      (value : Expression.t)
      : unit =
    let ty = Expression.type_of value in
    let sz = Types.size ty in
    let value =
    match ty with
    | Types.I32Type -> begin
      match value with
      | Num (I32 i) -> Num (I64 (Int64.of_int32 i))
      | _ -> value
    end
    | Types.I64Type -> value
    | Types.F32Type -> begin match value with
      | Num (F32 f) -> Num (I64 (Int64.bits_of_float (Int32.float_of_bits f)))
      | _ -> Cvtop (I32 I32.ReinterpretFloat, value)
    end
    | Types.F64Type -> begin match value with
      | Num (F64 f) -> Num (I64 f)
      | _ -> Cvtop (I64 I64.ReinterpretFloat, value)
    end
    in
    storen mem a o sz value

  let store_packed
      (sz : pack_size)
      (mem : MB.t)
      (a : address)
      (o : offset)
      (value : Expression.t) =
    let value : Expression.t =
      match value with
      | Num (I32 x) -> Num (I64 (Int64.of_int32 x))
      | Num (I64 x) -> Num (I64 x)
      | _ -> value
    in
    storen mem a o (length_pack_size sz) value

  let to_string = MB.to_string

end

module LazySMem : SymbolicMemory = SMem(LazyMemory)
module MapSMem : SymbolicMemory = SMem(MapMemory)
module TreeSMem : SymbolicMemory = SMem(TreeMemory)
