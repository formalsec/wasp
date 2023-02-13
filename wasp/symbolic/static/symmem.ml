type size = int32
type address = int64
type offset = int32

type memory = (int64, Symvalue.sym_expr) Hashtbl.t

(* Only store_byte, load_byte, from_symmem2, clone and to_string
   interact with the underlying data structure, this should make
   swapping it easy *)

type t = memory

exception Bounds

(* helper functions *)
let effective_address (a : address) (o : offset) : address =
  let ea = Int64.(add a (of_int32 o)) in
  if I64.lt_u ea a then raise Bounds;
  ea

let length_pack_size (sz : Memory.pack_size) : int =
  match sz with
  | Memory.Pack8 -> 1
  | Memory.Pack16 -> 2
  | Memory.Pack32 -> 4

let store_byte
    (mem : t)
    (a : address)
    (b : Symvalue.sym_expr) =
  Hashtbl.replace mem a b

let load_byte
    (mem : t)
    (a : address)
    : Symvalue.sym_expr =
  match Hashtbl.find_opt mem a with
  | Some b -> b
  | None -> Symvalue.Extract (Symvalue.Value (Values.I64 0L), 1, 0)

let storen
    (mem : t)
    (a : address)
    (o : offset)
    (n : int)
    (value : Symvalue.sym_expr)
    : unit =
  let rec loop mem a i n x =
    if n > i then begin
      store_byte mem a (Symvalue.Extract (x, i+1, i));
      loop mem (Int64.add a 1L) (i + 1) n x;
    end
  in loop mem (effective_address a o) 0 n value

let loadn
    (mem : t)
    (a : address)
    (o : offset)
    (n : int)
    : Symvalue.sym_expr list =
  let rec loop a n acc =
    if n = 0 then acc else begin
      let se = load_byte mem a in
      loop (Int64.sub a 1L) (n - 1) (se :: acc)
    end
  in loop Int64.(add (effective_address a o) (of_int (n - 1))) n []

(* public functions, visible in symmem.mli *)

let from_heap (mem : Heap.t) : t =
  let concolic_seq = (Heap.to_seq mem) in
  let concolic_to_symbolic (k, (_, s)) = (k, s) in
  Hashtbl.of_seq (Seq.map concolic_to_symbolic concolic_seq)

let clone (mem : t) : t =
  Hashtbl.copy mem

let load_value
    (mem : t)
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
  let expr = Symvalue.simplify ~extract:true expr in
  let open Values in
  let v =
  match ty with
    | Types.I32Type -> begin
      match expr with
      | Symvalue.Value (I64 v) -> Symvalue.Value (I32 (Int64.to_int32 v))
      | Symvalue.Ptr   (I64 p) -> Symvalue.Ptr   (I32 (Int64.to_int32 p))
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
  let open Symvalue in
  let v =
  match v with
  | Extract ((Value I32 i), h, l) ->
    let i = Int64.of_int32 i in
    let len = h - l in
    begin match len with
    | 8 -> Symvalue.Value (I64                 (nland64 (Int64.shift_right i (l * 8)) (h - l)))
    | 4 -> Symvalue.Value (I32 (Int64.to_int32 (nland64 (Int64.shift_right i (l * 8)) (h - l))))
    | _ -> failwith "we assume to be reading i32 or i64 for now"
    end
  | Extract ((Value I64 i), h, l) ->
    let len = h - l in
    begin match len with
    | 8 -> Value (I64                 (nland64 (Int64.shift_right i (l * 8)) (h - l)))
    | 4 -> Value (I32 (Int64.to_int32 (nland64 (Int64.shift_right i (l * 8)) (h - l))))
    | _ -> failwith "we assume to be reading i32 or i64 for now"
    end
  | Extract (Symbolic (SymInt32, x), 4, 0) ->
      Symbolic (SymInt32, x)
  | Extract (Symbolic (SymInt64, x), 8, 0) ->
      Symbolic (SymInt64, x)
  | Extract (I32Binop (op, a, b), 4, 0) ->
      I32Binop (op, a, b)
  | Extract (I64Binop (op, a, b), 8, 0) ->
      I64Binop (op, a, b)
  | Extract ((SymPtr (base, offset)), 4, 0) ->
      SymPtr (base, offset)
  | Extract (Extract (i, 4, 0), 4, 0) ->
      Extract (i, 4, 0)
  | Extract (Extract (i, 8, 0), 8, 0) ->
      Extract (i, 8, 0)
  | F32Cvtop (Sf32.F32ReinterpretInt, (Extract ((Value I64 i), h, l))) ->
    let len = h - l in
    let ix = match len with
    | 4 -> (Int64.to_int32 (nland64 (Int64.shift_right i (l * 8)) (h - l)))
    | _ -> failwith "we assume to be reading i32 or i64 for now"
    in
    Value (F32 (F32.of_bits ix))
  | _ -> v
  in
  v

let load_packed
    (sz : Memory.pack_size)
    (mem : t)
    (a : address)
    (o : offset)
    (ty : Types.value_type) :
    Symvalue.sym_expr =
  let exprs = loadn mem a o (length_pack_size sz) in
  let expr = Symvalue.simplify ~extract:true List.(
    fold_left (fun acc e -> Symvalue.Concat (e, acc)) (hd exprs) (tl exprs)
  )
  in
  let open Values in
  let v =
  match ty with
    | Types.I32Type -> begin
      match expr with
      | Symvalue.Value (I64 v) -> Symvalue.Value (I32 (Int64.to_int32 v))
      | Symvalue.Ptr   (I64 p) -> Symvalue.Ptr   (I32 (Int64.to_int32 p))
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
  let open Symvalue in
  let v =
  match v with
  | Extract ((Value I64 i), h, l) ->
    let len = h - l in
    begin match len with
    | 8 -> Symvalue.Value (I64                 (nland64 (Int64.shift_right i (l * 8)) (h - l)))
    | 4 -> Symvalue.Value (I32 (Int64.to_int32 (nland64 (Int64.shift_right i (l * 8)) (h - l))))
    | _ -> failwith "we assume to be reading i32 or i64 for now"
    end
  | Extract (Symbolic (SymInt32, x), 4, 0) ->
      Symbolic (SymInt32, x)
  | Extract (Symbolic (SymInt64, x), 8, 0) ->
      Symbolic (SymInt64, x)
  | Extract (I32Binop (op, a, b), 4, 0) ->
      I32Binop (op, a, b)
  | Extract (I64Binop (op, a, b), 8, 0) ->
      I64Binop (op, a, b)
  | Extract ((SymPtr (base, offset)), 4, 0) ->
      SymPtr (base, offset)
  | Extract (Extract (i, 4, 0), 4, 0) ->
      Extract (i, 4, 0)
  | Extract (Extract (i, 8, 0), 8, 0) ->
      Extract (i, 8, 0)
  | F32Cvtop (Sf32.F32ReinterpretInt, (Extract ((Value I64 i), h, l))) ->
    let len = h - l in
    let ix = match len with
    | 4 -> (Int64.to_int32 (nland64 (Int64.shift_right i (l * 8)) (h - l)))
    | _ -> failwith "we assume to be reading i32 or i64 for now"
    in
    Value (F32 (F32.of_bits ix))
  | _ ->
    let rec loop acc i =
      if i >= (Types.size ty) then acc
      else loop (acc @ [Extract (Value (I64 0L), 1, 0)]) (i + 1) in
    let exprs = loop exprs (List.length exprs) in
    List.(
      fold_left (fun acc e -> Concat (e, acc)) (hd exprs) (tl exprs)
    )
  in
  v

let load_string (mem : t) (a : address) : string =
  let rec loop a acc =
    let sb = load_byte mem a in
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
    (mem : t)
    (a : address)
    (o : offset)
    (value : Symvalue.sym_expr)
    : unit =
  let ty = Symvalue.type_of value in
  let sz = Types.size ty in
  let open Values in
  let value =
  match ty with
  | Types.I32Type
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
    (mem : t)
    (a : address)
    (o : offset)
    (value : Symvalue.sym_expr) =
  storen mem a o (length_pack_size sz) value

let to_string (mem : t) : string =
  (* TODO: need to go all the way up the chain *)
  let lst = List.sort (fun (a, _) (b, _) -> compare a b) (List.of_seq (Hashtbl.to_seq mem)) in
  List.fold_right (
    fun (a, se) acc ->
      "(" ^ (Int64.to_string a) ^ "->" ^
      "(" ^ (Symvalue.to_string se) ^ ")" ^
      ")\n" ^ acc
  ) lst ""
