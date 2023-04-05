open Encoding
open Types
open Expression
open Interpreter.Memory

type size = int32
type address = int64
type offset = int32
type store = int * Expression.t
type memory = (address, store) Hashtbl.t
type t = { map : memory; parent : t option }

exception Bounds
exception InvalidAddress of address

let packed_size = function Pack8 -> 1 | Pack16 -> 2 | Pack32 -> 4
let alloc (sz : int) : t = { map = Hashtbl.create sz; parent = None }

let size (h : t) : int =
  let rec size' accum = function
    | None -> accum
    | Some h' -> size' (Hashtbl.length h'.map + accum) h'.parent
  in
  size' (Hashtbl.length h.map) h.parent

let memcpy (h : t) : t = { map = Hashtbl.copy h.map; parent = h.parent }

let to_seq (h : t) : (address * store) Seq.t =
  let rec to_seq' (acc : (address * store) Seq.t) = function
    | None -> acc
    | Some h' -> to_seq' (Seq.append (Hashtbl.to_seq h'.map) acc) h'.parent
  in
  to_seq' (Hashtbl.to_seq h.map) h.parent

let clone (h : t) : t * t =
  ( {
      map = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
      parent = Some h;
    },
    {
      map = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
      parent = Some h;
    } )

let add_seq (h : t) (l : (address * store) Seq.t) : unit =
  Seq.iter (fun (a, s) -> Hashtbl.replace h.map a s) l

let to_list (h : t) : (address * store) list =
  Hashtbl.fold (fun a s acc -> (a, s) :: acc) h.map []

let to_string (mem : t) : string =
  let lst = List.sort (fun (a, _) (b, _) -> compare a b) (to_list mem) in
  List.fold_right
    (fun (a, (v, e)) b ->
      "(" ^ Int64.to_string a ^ "->" ^ "(" ^ string_of_int v ^ ", "
      ^ Expression.to_string e ^ ")" ^ ")\n" ^ b)
    lst ""

let store_byte (h : t) (a : address) (b : store) : unit =
  Hashtbl.replace h.map a b

let load_byte (h : t) (a : address) : store =
  let rec load_byte' heap =
    match Hashtbl.find_opt heap.map a with
    | Some b -> Some b
    | None -> Option.bind heap.parent load_byte'
  in
  match Hashtbl.find_opt h.map a with
  | Some b -> b
  | None -> (
      match Option.bind h.parent load_byte' with
      | Some b -> b
      | None -> (0, Extract (Val (Num (I64 0L)), 1, 0)))

let concat bs = List.(fold_left (fun acc e -> e ++ acc) (hd bs) (tl bs))

let load_bytes (h : t) (a : address) (n : int) : string * Expression.t =
  let buf = Buffer.create n in
  let rec rec_loop i acc =
    if i = n - 1 then acc
    else
      let chr, schr = load_byte h Int64.(add a (of_int i)) in
      Buffer.add_char buf (Char.chr chr);
      rec_loop (i + 1) (schr :: acc)
  in
  let schrs = simplify (concat (rec_loop 0 [])) in
  (Buffer.contents buf, schrs)

let load_string (h : t) (a : address) : string =
  let rec loop a acc =
    let c, _ = load_byte h a in
    if c = 0 then acc else loop (Int64.add a 1L) (acc ^ Char.(escaped (chr c)))
  in
  loop a ""

let store_bytes (h : t) (a : address) (bs : string) : unit =
  for i = String.length bs - 1 downto 0 do
    let b = Char.code bs.[i] in
    let sb = Extract (Val (Num (I64 (Int64.of_int b))), 1, 0) in
    store_byte h Int64.(add a (of_int i)) (b, sb)
  done

let effective_address (a : Int64.t) (o : offset) : address =
  let ea = Int64.(add a (of_int32 o)) in
  if Eval_numeric.eval_relop (I64 I64.LtU) (I64 ea) (I64 a) then raise Bounds;
  ea

let loadn (h : t) (a : address) (o : offset) (n : int) =
  assert (n > 0 && n <= 8);
  let rec loop a n acc =
    if n = 0 then acc
    else
      let x, lacc = acc and cv, se = load_byte h a in
      let x' = Int64.(logor (of_int cv) (shift_left x 8)) in
      loop (Int64.sub a 1L) (n - 1) (x', se :: lacc)
  in
  loop Int64.(add (effective_address a o) (of_int (n - 1))) n (0L, [])

let storen (h : t) (a : address) (o : offset) (n : int)
    (x : int64 * Expression.t) : unit =
  assert (n > 0 && n <= 8);
  let rec loop a i n x =
    if n > i then (
      let cv, se = x in
      let b = Int64.to_int cv land 0xff in
      store_byte h a (b, Extract (se, i + 1, i));
      loop (Int64.add a 1L) (i + 1) n (Int64.shift_right cv 8, se))
  in
  loop (effective_address a o) 0 n x

let load_value (h : t) (a : address) (o : offset) (t : num_type) :
    Num.t * Expression.t =
  let n, exprs = loadn h a o (Types.size_of_num_type t) in
  let expr = simplify ~extract:true (simplify (concat exprs)) in
  let (n' : Num.t), (expr' : Expression.t) =
    match t with
    | `I32Type ->
        let e =
          match expr with
          | Val (Num (I64 n)) -> Val (Num (I32 (Int64.to_int32 n)))
          | _ -> expr
        in
        (I32 (Int64.to_int32 n), e)
    | `I64Type -> (I64 n, expr)
    | `F32Type ->
        let e =
          match expr with
          | Val (Num (I64 v)) -> Val (Num (F32 (Int64.to_int32 v)))
          | Cvtop (I32 I32.ReinterpretFloat, v) -> v
          | _ -> Cvtop (F32 F32.ReinterpretInt, expr)
        in
        (F32 (Int64.to_int32 n), e)
    | `F64Type ->
        let e =
          match expr with
          | Val (Num (I64 n)) -> Val (Num (F64 n))
          | Cvtop (I64 I64.ReinterpretFloat, v) -> v
          | _ -> Cvtop (F64 F64.ReinterpretInt, expr)
        in
        (F64 n, e)
  in
  (n', expr')

let store_value (h : t) (a : address) (o : offset) (v : Num.t * Expression.t) :
    unit =
  let cv, sv = v in
  let cv', (sv' : Expression.t) =
    match cv with
    | I32 x ->
        let e =
          match sv with
          | Val (Num (I32 x)) -> Val (Num (I64 (Int64.of_int32 x)))
          | _ -> sv
        in
        (Int64.of_int32 x, e)
    | I64 x -> (x, sv)
    | F32 x ->
        let e =
          match sv with
          | Val (Num (F32 n)) -> Val (Num (I64 (Int64.of_int32 n)))
          | _ -> Cvtop (I32 I32.ReinterpretFloat, sv)
        in
        (Int64.of_int32 x, e)
    | F64 x ->
        let e =
          match sv with
          | Val (Num (F64 x)) -> Val (Num (I64 x))
          | _ -> Cvtop (I64 I64.ReinterpretFloat, sv)
        in
        (x, e)
  in
  storen h a o (Types.size (Types.type_of_num cv)) (cv', sv')

let extend x n = function
  | ZX -> x
  | SX ->
      let sh = 64 - (8 * n) in
      Int64.(shift_right (shift_left x sh) sh)

let load_packed (sz : pack_size) (ext : extension) (h : t) (a : address)
    (o : offset) (t : num_type) : Num.t * Expression.t =
  let n = packed_size sz in
  let cv, sv = loadn h a o n in
  let cv = extend cv n ext in
  let x' : Num.t =
    match t with
    | `I32Type -> I32 (Int64.to_int32 cv)
    | `I64Type -> I64 cv
    | _ -> raise Type
  in
  let sv' : Expression.t =
    match simplify ~extract:true (simplify (concat sv)) with
    | Val (Num (I64 x)) -> (
        match t with
        | `I32Type -> Val (Num (I32 (Int64.to_int32 x)))
        | _ -> Val (Num (I64 x)))
    | SymPtr (b, o) -> SymPtr (b, o)
    | _ ->
        let rec loop acc i =
          if i >= Types.size_of_num_type t then acc
          else loop (acc @ [ Extract (Val (Num (I64 0L)), 1, 0) ]) (i + 1)
        in
        concat (loop sv (List.length sv))
  in
  (x', sv')

let store_packed (sz : pack_size) (h : t) (a : address) (o : offset)
    (v : Num.t * Expression.t) : unit =
  let n = packed_size sz in
  let cv, sv = v in
  let x =
    match cv with I32 x -> Int64.of_int32 x | I64 x -> x | _ -> raise Type
  in
  let sx : Expression.t =
    match sv with
    | Val (Num (I32 x)) -> Val (Num (I64 (Int64.of_int32 x)))
    | Val (Num (I64 x)) -> Val (Num (I64 x))
    | _ -> sv
  in
  storen h a o n (x, sx)

let update (h : t) (store : Store.t) : unit =
  let eval_heap heap sto =
    Hashtbl.iter
      (fun a (_, se) ->
        let i =
          match Store.eval store se with
          | I32 x -> Int32.to_int x
          | I64 x -> Int64.to_int x
          | F32 x -> Int32.to_int x
          | F64 x -> Int64.to_int x
        in
        store_byte heap a (i, se))
      heap.map
  in
  let rec update' = function
    | None -> ()
    | Some h' ->
        eval_heap h' store;
        update' h'.parent
  in
  eval_heap h store;
  update' h.parent
