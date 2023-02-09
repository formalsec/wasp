open Types
open Values
open Symvalue

type size = int32
type address = int64
type offset = int32
type store = int * sym_expr
type memory = (address, store) Hashtbl.t
type t = memory

exception Bounds
exception InvalidAddress of address

let packed_size = function
  | Memory.Pack8 -> 1
  | Memory.Pack16 -> 2
  | Memory.Pack32 -> 4

let alloc (sz : int) : memory = Hashtbl.create sz
let size (mem : memory) : int = Hashtbl.length mem
let clear (mem : memory) : unit = Hashtbl.clear mem
let memcpy (mem : memory) : memory = Hashtbl.copy mem
let to_seq (mem : memory) = Hashtbl.to_seq mem

let add_seq (mem : memory) (l : (address * store) Seq.t) : unit =
  Seq.iter (fun (a, s) -> Hashtbl.replace mem a s) l

let to_list (mem : memory) : (address * store) list =
  Hashtbl.fold (fun a s acc -> (a, s) :: acc) mem []

let to_string (mem : memory) : string =
  let lst = List.sort (fun (a, _) (b, _) -> compare a b) (to_list mem) in
  List.fold_right
    (fun (a, (v, e)) b ->
      "(" ^ Int64.to_string a ^ "->" ^ "(" ^ string_of_int v ^ ", "
      ^ Symvalue.to_string e ^ ")" ^ ")\n" ^ b)
    lst ""

let load_byte (mem : memory) (a : address) : store =
  try Hashtbl.find mem a with Not_found -> (0, Extract (Value (I64 0L), 1, 0))

let store_byte (mem : memory) (a : address) (b : store) : unit =
  Hashtbl.replace mem a b

let load_bytes (mem : memory) (a : address) (n : int) : string * sym_expr =
  let buf = Buffer.create n in
  let rec rec_loop i acc =
    if i = n - 1 then acc
    else
      let chr, schr = load_byte mem Int64.(add a (of_int i)) in
      Buffer.add_char buf (Char.chr chr);
      rec_loop (i + 1) (schr :: acc)
  in
  let schrs = rec_loop 0 [] in
  let schrs' =
    simplify
      List.(fold_left (fun acc e -> Concat (e, acc)) (hd schrs) (tl schrs))
  in
  (Buffer.contents buf, schrs')

let load_string (mem : memory) (a : address) : string =
  let rec loop a acc =
    let c, _ = load_byte mem a in
    if c = 0 then acc else loop (Int64.add a 1L) (acc ^ Char.(escaped (chr c)))
  in
  loop a ""

let store_bytes (mem : memory) (a : address) (bs : string) : unit =
  for i = String.length bs - 1 downto 0 do
    let b = Char.code bs.[i] in
    let sb = Extract (Value (I64 (Int64.of_int b)), 1, 0) in
    store_byte mem Int64.(add a (of_int i)) (b, sb)
  done

let effective_address (a : I64.t) (o : offset) : address =
  let ea = Int64.(add a (of_int32 o)) in
  if I64.lt_u ea a then raise Bounds;
  ea

let loadn (mem : memory) (a : address) (o : offset) (n : int) =
  assert (n > 0 && n <= 8);
  let rec loop a n acc =
    if n = 0 then acc
    else
      let x, lacc = acc and cv, se = load_byte mem a in
      let x' = Int64.(logor (of_int cv) (shift_left x 8)) in
      loop (Int64.sub a 1L) (n - 1) (x', se :: lacc)
  in
  loop Int64.(add (effective_address a o) (of_int (n - 1))) n (0L, [])

let storen (mem : memory) (a : address) (o : offset) (n : int)
    (x : int64 * sym_expr) : unit =
  assert (n > 0 && n <= 8);
  let rec loop a i n x =
    if n > i then (
      let cv, se = x in
      let b = Int64.to_int cv land 0xff in
      store_byte mem a (b, Extract (se, i + 1, i));
      loop (Int64.add a 1L) (i + 1) n (Int64.shift_right cv 8, se))
  in
  loop (effective_address a o) 0 n x

let load_value (mem : memory) (a : address) (o : offset) (t : value_type) :
    sym_value =
  let n, exprs = loadn mem a o (Types.size t) in
  (* Concat symbolic byte list *)
  let expr =
    simplify
      List.(fold_left (fun acc e -> Concat (e, acc)) (hd exprs) (tl exprs))
  in
  let n' =
    match t with
    | I32Type -> I32 (Int64.to_int32 n)
    | I64Type -> I64 n
    | F32Type -> F32 (F32.of_bits (Int64.to_int32 n))
    | F64Type -> F64 (F64.of_bits n)
  in
  let expr' = simplify ~extract:true expr in
  let expr' : sym_expr =
    match t with
    | I32Type -> (
        match expr' with
        | Value (I64 v) -> Value (I32 (Int64.to_int32 v))
        | Ptr (I64 p) -> Ptr (I32 (Int64.to_int32 p))
        | _ -> expr')
    | I64Type -> expr'
    | F32Type -> (
        match expr' with
        | Value (I64 v) -> Value (F32 (F32.of_bits (Int64.to_int32 v)))
        | I32Cvtop (Si32.I32ReinterpretFloat, v) -> v
        | _ -> F32Cvtop (Sf32.F32ReinterpretInt, expr'))
    | F64Type -> (
        match expr' with
        | Value (I64 v) -> Value (F64 (F64.of_bits v))
        | I64Cvtop (Si64.I64ReinterpretFloat, v) -> v
        | _ -> F64Cvtop (Sf64.F64ReinterpretInt, expr'))
  in
  (n', expr')

let store_value (mem : memory) (a : address) (o : offset) (v : sym_value) : unit
    =
  let cv, sv = v in
  let x =
    match cv with
    | I32 x -> Int64.of_int32 x
    | I64 x -> x
    | F32 x -> Int64.of_int32 (F32.to_bits x)
    | F64 x -> F64.to_bits x
  in
  let sv : sym_expr =
    match Values.type_of cv with
    | I32Type -> (
        match sv with
        | Value (I32 x) -> Value (I64 (Int64.of_int32 x))
        | Ptr (I32 x) -> Ptr (I64 (Int64.of_int32 x))
        | _ -> sv)
    | I64Type -> sv
    | F32Type -> (
        match sv with
        | Value (F32 x) -> Value (I64 (Int64.of_int32 (F32.to_bits x)))
        | _ -> I32Cvtop (Si32.I32ReinterpretFloat, sv))
    | F64Type -> (
        match sv with
        | Value (F64 x) -> Value (I64 (F64.to_bits x))
        | _ -> I64Cvtop (Si64.I64ReinterpretFloat, sv))
  in
  storen mem a o (Types.size (Values.type_of cv)) (x, sv)

let extend x n = function
  | Memory.ZX -> x
  | Memory.SX ->
      let sh = 64 - (8 * n) in
      Int64.(shift_right (shift_left x sh) sh)

let load_packed (sz : Memory.pack_size) (ext : Memory.extension) (mem : memory)
    (a : address) (o : offset) (t : value_type) : sym_value =
  let n = packed_size sz in
  let cv, sv = loadn mem a o n in
  let cv = extend cv n ext in
  let x' =
    match t with
    | I32Type -> I32 (Int64.to_int32 cv)
    | I64Type -> I64 cv
    | _ -> raise Memory.Type
  in
  let sv' =
    simplify List.(fold_left (fun acc e -> Concat (e, acc)) (hd sv) (tl sv))
  in
  let sv'' : sym_expr =
    match simplify ~extract:true sv' with
    | Value (I64 x) -> (
        match t with
        | I32Type -> Value (I32 (Int64.to_int32 x))
        | _ -> Value (I64 x))
    | Ptr p -> Ptr p
    | _ ->
        let rec loop acc i =
          if i >= Types.size t then acc
          else loop (acc @ [ Extract (Value (I64 0L), 1, 0) ]) (i + 1)
        in
        let exprs = loop sv (List.length sv) in
        List.(fold_left (fun acc e -> Concat (e, acc)) (hd exprs) (tl exprs))
  in
  (x', sv'')

let store_packed (sz : Memory.pack_size) (mem : memory) (a : address)
    (o : offset) (v : sym_value) : unit =
  let n = packed_size sz in
  let cv, sv = v in
  let x =
    match cv with
    | I32 x -> Int64.of_int32 x
    | I64 x -> x
    | _ -> raise Memory.Type
  in
  let sx : sym_expr =
    match sv with
    | Value (I32 x) -> Value (I64 (Int64.of_int32 x))
    | Value (I64 x) -> Value (I64 x)
    | _ -> sv
  in
  storen mem a o n (x, sx)

let update (mem : memory) (store : Store.t) : unit =
  Hashtbl.iter
    (fun a (_, se) ->
      let i =
        match Store.eval store se with
        | I32 x -> Int32.to_int x
        | I64 x -> Int64.to_int x
        | F32 x -> Int32.to_int (F32.to_bits x)
        | F64 x -> Int64.to_int (F64.to_bits x)
      in
      store_byte mem a (i, se))
    mem
