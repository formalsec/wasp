open Smtml
open Interpreter.Memory

type size = int32

type address = int64

type offset = int32

type store = int * Expr.t

type memory = (address, store) Hashtbl.t

type t =
  { map : memory
  ; parent : t option
  }

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
  ( { map = Hashtbl.create Interpreter.Flags.hashtbl_default_size
    ; parent = Some h
    }
  , { map = Hashtbl.create Interpreter.Flags.hashtbl_default_size
    ; parent = Some h
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
      ^ Expr.to_string e ^ ")" ^ ")\n" ^ b )
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
    | None -> (0, Expr.make (Extract (Expr.value (Num (I64 0L)), 1, 0))) )

let concat bs = List.(fold_left (fun acc e -> Expr.concat e acc) (hd bs) (tl bs))

let load_bytes (h : t) (a : address) (n : int) : string * Expr.t =
  let buf = Buffer.create n in
  let rec rec_loop i acc =
    if i = n - 1 then acc
    else
      let chr, schr = load_byte h Int64.(add a (of_int i)) in
      Buffer.add_char buf (Char.chr chr);
      rec_loop (i + 1) (schr :: acc)
  in
  let schrs = Expr.simplify (concat (rec_loop 0 [])) in
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
    let sb =
      Expr.(extract (value (Num (I64 (Int64.of_int b)))) ~high:1 ~low:0)
    in
    store_byte h Int64.(add a (of_int i)) (b, sb)
  done

let effective_address (a : Int64.t) (o : offset) : address =
  let ea = Int64.(add a (of_int32 o)) in
  if Smtml.Eval.relop (Ty_bitv 64) LtU (Num (I64 ea)) (Num (I64 a)) then
    raise Bounds;
  ea

let loadn (h : t) (a : address) (o : offset) (n : int) =
  assert (n > 0 && n <= 8);
  let rec loop a n acc =
    if n = 0 then acc
    else
      let x, lacc = acc
      and cv, se = load_byte h a in
      let x' = Int64.(logor (of_int cv) (shift_left x 8)) in
      loop (Int64.sub a 1L) (n - 1) (x', se :: lacc)
  in
  loop Int64.(add (effective_address a o) (of_int (n - 1))) n (0L, [])

let storen (h : t) (a : address) (o : offset) (n : int) (x : int64 * Expr.t) :
  unit =
  assert (n > 0 && n <= 8);
  let rec loop a i n x =
    if n > i then (
      let concrete, symbolic = x in
      let b = Int64.to_int concrete land 0xff in
      store_byte h a (b, Expr.make @@ Extract (symbolic, i + 1, i));
      loop (Int64.add a 1L) (i + 1) n (Int64.shift_right concrete 8, symbolic) )
  in
  loop (effective_address a o) 0 n x

let load_value (h : t) (a : address) (o : offset) (t : Ty.t) : Num.t * Expr.t =
  let n, exprs = loadn h a o (Ty.size t) in
  let expr = Expr.simplify (Expr.simplify (concat exprs)) in
  let (n' : Num.t), (expr' : Expr.t) =
    match t with
    | Ty.Ty_bitv 32 ->
      let e =
        match Expr.view expr with
        | Val (Num (I64 _)) -> Expr.value (Num (I32 (Int64.to_int32 n)))
        | _ -> expr
      in
      (I32 (Int64.to_int32 n), e)
    | Ty.Ty_bitv 64 -> (I64 n, expr)
    | Ty.Ty_fp 32 ->
      let e =
        match Expr.view expr with
        | Val (Num (I64 v)) -> Expr.value (Num (F32 (Int64.to_int32 v)))
        | Cvtop (Ty.Ty_bitv 32, Reinterpret_float, v) -> v
        | _ -> Expr.cvtop (Ty.Ty_fp 32) Reinterpret_int expr
      in
      (F32 (Int64.to_int32 n), e)
    | Ty.Ty_fp 64 ->
      let e =
        match Expr.view expr with
        | Val (Num (I64 n)) -> Expr.value (Num (F64 n))
        | Cvtop (Ty.Ty_bitv 64, Reinterpret_float, v) -> v
        | _ -> Expr.cvtop (Ty_fp 64) Reinterpret_int expr
      in
      (F64 n, e)
    | _ -> assert false
  in
  (n', expr')

let store_value (h : t) (a : address) (o : offset) (v : Num.t * Expr.t) : unit =
  let cv, sv = v in
  let cv', (sv' : Expr.t) =
    match cv with
    | I32 x ->
      let e =
        match Expr.view sv with
        | Val (Num (I32 x)) -> Expr.value (Num (I64 (Int64.of_int32 x)))
        | _ -> sv
      in
      (Int64.of_int32 x, e)
    | I64 x -> (x, sv)
    | F32 x ->
      let e =
        match Expr.view sv with
        | Val (Num (F32 n)) -> Expr.value (Num (I64 (Int64.of_int32 n)))
        | _ -> Expr.cvtop (Ty_bitv 32) Reinterpret_float sv
      in
      (Int64.of_int32 x, e)
    | F64 x ->
      let e =
        match Expr.view sv with
        | Val (Num (F64 x)) -> Expr.value (Num (I64 x))
        | _ -> Expr.cvtop (Ty_bitv 64) Reinterpret_float sv
      in
      (x, e)
    | _ -> assert false
  in
  storen h a o (Ty.size (Num.type_of cv)) (cv', sv')

let extend x n = function
  | ZX -> x
  | SX ->
    let sh = 64 - (8 * n) in
    Int64.(shift_right (shift_left x sh) sh)

let load_packed (sz : pack_size) (ext : extension) (h : t) (a : address)
  (o : offset) (t : Ty.t) : Num.t * Expr.t =
  let n = packed_size sz in
  let cv, sv = loadn h a o n in
  let cv = extend cv n ext in
  let x' : Num.t =
    match t with
    | Ty_bitv 32 -> I32 (Int64.to_int32 cv)
    | Ty_bitv 64 -> I64 cv
    | _ -> raise Type
  in
  let sv' : Expr.t =
    let v = Expr.simplify (Expr.simplify (concat sv)) in
    match Expr.view v with
    | Val (Num (I64 x)) -> (
      match t with
      | Ty_bitv 32 -> Expr.value (Num (I32 (Int64.to_int32 x)))
      | _ -> v )
    | Ptr _ -> v
    | _ ->
      let rec loop acc i =
        if i >= Ty.size t then acc
        else
          loop
            (acc @ [ Expr.make @@ Extract (Expr.value (Num (I64 0L)), 1, 0) ])
            (i + 1)
      in
      concat (loop sv (List.length sv))
  in
  (x', sv')

let store_packed (sz : pack_size) (h : t) (a : address) (o : offset)
  (v : Num.t * Expr.t) : unit =
  let n = packed_size sz in
  let cv, sv = v in
  let x =
    match cv with I32 x -> Int64.of_int32 x | I64 x -> x | _ -> raise Type
  in
  let sx : Expr.t =
    match Expr.view sv with
    | Val (Num (I32 x)) -> Expr.value (Num (I64 (Int64.of_int32 x)))
    | _ -> sv
  in
  storen h a o n (x, sx)

let update (h : t) (store : Store.t) : unit =
  let eval_heap heap sto =
    Hashtbl.iter
      (fun a (_, se) ->
        let i =
          match Store.eval sto se with
          | Num (I32 x) -> Int32.to_int x
          | Num (I64 x) -> Int64.to_int x
          | Num (F32 x) -> Int32.to_int x
          | Num (F64 x) -> Int64.to_int x
          | _ -> assert false
        in
        store_byte heap a (i, se) )
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
