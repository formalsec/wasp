open Encoding
open Types
open Expression
open Interpreter.Memory

type size = int32
type address = int64
type offset = int32
type store = int * Expression.t
type memory = (address, store) Hashtbl.t
type t = memory

exception Bounds
exception InvalidAddress of address

let packed_size = function Pack8 -> 1 | Pack16 -> 2 | Pack32 -> 4
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
      ^ Expression.to_string e ^ ")" ^ ")\n" ^ b)
    lst ""

let load_byte (mem : memory) (a : address) : store =
  try Hashtbl.find mem a with Not_found -> (0, Extract (Num (I64 0L), 1, 0))

let store_byte (mem : memory) (a : address) (b : store) : unit =
  Hashtbl.replace mem a b

let concat bs = List.(fold_left (fun acc e -> e ++ acc) (hd bs) (tl bs))

let load_bytes (mem : memory) (a : address) (n : int) : string * Expression.t =
  let buf = Buffer.create n in
  let rec rec_loop i acc =
    if i = n - 1 then acc
    else
      let chr, schr = load_byte mem Int64.(add a (of_int i)) in
      Buffer.add_char buf (Char.chr chr);
      rec_loop (i + 1) (schr :: acc)
  in
  let schrs = simplify (concat (rec_loop 0 [])) in
  (Buffer.contents buf, schrs)

let load_string (mem : memory) (a : address) : string =
  let rec loop a acc =
    let c, _ = load_byte mem a in
    if c = 0 then acc else loop (Int64.add a 1L) (acc ^ Char.(escaped (chr c)))
  in
  loop a ""

let store_bytes (mem : memory) (a : address) (bs : string) : unit =
  for i = String.length bs - 1 downto 0 do
    let b = Char.code bs.[i] in
    let sb = Extract (Num (I64 (Int64.of_int b)), 1, 0) in
    store_byte mem Int64.(add a (of_int i)) (b, sb)
  done

let effective_address (a : Int64.t) (o : offset) : address =
  let ea = Int64.(add a (of_int32 o)) in
  if Eval_numeric.eval_relop (I64 I64.LtU) (I64 ea) (I64 a) then raise Bounds;
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
    (x : int64 * Expression.t) : unit =
  assert (n > 0 && n <= 8);
  let rec loop a i n x =
    if n > i then (
      let cv, se = x in
      let b = Int64.to_int cv land 0xff in
      store_byte mem a (b, Extract (se, i + 1, i));
      loop (Int64.add a 1L) (i + 1) n (Int64.shift_right cv 8, se))
  in
  loop (effective_address a o) 0 n x

let load_value (mem : memory) (a : address) (o : offset) (t : num_type) : value
    =
  let n, exprs = loadn mem a o (Types.size t) in
  let expr = simplify ~extract:true (simplify (concat exprs)) in
  let (n' : Num.t), (expr' : Expression.t) =
    match t with
    | I32Type ->
        let e =
          match expr with
          | Num (I64 n) -> Num (I32 (Int64.to_int32 n))
          | _ -> expr
        in
        (I32 (Int64.to_int32 n), e)
    | I64Type -> (I64 n, expr)
    | F32Type ->
        let e =
          match expr with
          | Num (I64 v) -> Num (F32 (Int64.to_int32 v))
          | Cvtop (I32 I32.ReinterpretFloat, v) -> v
          | _ -> Cvtop (F32 F32.ReinterpretInt, expr)
        in
        (F32 (Int64.to_int32 n), e)
    | F64Type ->
        let e =
          match expr with
          | Num (I64 n) -> Num (F64 n)
          | Cvtop (I64 I64.ReinterpretFloat, v) -> v
          | _ -> Cvtop (F64 F64.ReinterpretInt, expr)
        in
        (F64 n, e)
    | _ -> assert false
  in
  (n', expr')

let store_value (mem : memory) (a : address) (o : offset) (v : value) : unit =
  let cv, sv = v in
  let cv', (sv' : Expression.t) =
    match cv with
    | I32 x ->
        let e =
          match sv with Num (I32 x) -> Num (I64 (Int64.of_int32 x)) | _ -> sv
        in
        (Int64.of_int32 x, e)
    | I64 x -> (x, sv)
    | F32 x ->
        let e =
          match sv with
          | Num (F32 n) -> Num (I64 (Int64.of_int32 n))
          | _ -> Cvtop (I32 I32.ReinterpretFloat, sv)
        in
        (Int64.of_int32 x, e)
    | F64 x ->
        let e =
          match sv with
          | Num (F64 x) -> Num (I64 x)
          | _ -> Cvtop (I64 I64.ReinterpretFloat, sv)
        in
        (x, e)
    | _ -> assert false
  in
  storen mem a o (Types.size (Types.type_of_num cv)) (cv', sv')

let extend x n = function
  | ZX -> x
  | SX ->
      let sh = 64 - (8 * n) in
      Int64.(shift_right (shift_left x sh) sh)

let load_packed (sz : pack_size) (ext : extension) (mem : memory) (a : address)
    (o : offset) (t : num_type) : value =
  let n = packed_size sz in
  let cv, sv = loadn mem a o n in
  let cv = extend cv n ext in
  let x' : Num.t =
    match t with
    | I32Type -> I32 (Int64.to_int32 cv)
    | I64Type -> I64 cv
    | _ -> raise Type
  in
  let sv' : Expression.t =
    match simplify ~extract:true (simplify (concat sv)) with
    | Num (I64 x) -> (
        match t with
        | I32Type -> Num (I32 (Int64.to_int32 x))
        | _ -> Num (I64 x))
    | SymPtr (b, o) -> SymPtr (b, o)
    | _ ->
        let rec loop acc i =
          if i >= Types.size t then acc
          else loop (acc @ [ Extract (Num (I64 0L), 1, 0) ]) (i + 1)
        in
        concat (loop sv (List.length sv))
  in
  (x', sv')

let store_packed (sz : pack_size) (mem : memory) (a : address) (o : offset)
    (v : value) : unit =
  let n = packed_size sz in
  let cv, sv = v in
  let x =
    match cv with I32 x -> Int64.of_int32 x | I64 x -> x | _ -> raise Type
  in
  let sx : Expression.t =
    match sv with
    | Num (I32 x) -> Num (I64 (Int64.of_int32 x))
    | Num (I64 x) -> Num (I64 x)
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
        | F32 x -> Int32.to_int x
        | F64 x -> Int64.to_int x
        | _ -> assert false
      in
      store_byte mem a (i, se))
    mem
