open Common
open Encoding
open Encoding.Types
open Encoding.Expression

type name = string
type bind = name * Num.t

type store = {
  sym : name Counter.t;
  ord : name BatDynArray.t;
  map : (name, Num.t) Hashtbl.t;
}

type t = store

let reset (s : t) : unit =
  Counter.clear s.sym;
  Hashtbl.clear s.map;
  BatDynArray.clear s.ord

let copy (s : t) : t =
  let sym = Counter.copy s.sym
  and ord = BatDynArray.copy s.ord
  and map = Hashtbl.copy s.map in
  { sym; ord; map }

let clear (s : t) : unit = Hashtbl.clear s.map

let init (s : t) (binds : (string * Expression.value) list) : unit =
  List.iter
    (fun (x, v) ->
      match v with Num n -> Hashtbl.replace s.map x n | _ -> assert false)
    binds

let from_parts (sym : name Counter.t) (ord : name BatDynArray.t)
    (map : (name, Num.t) Hashtbl.t) : t =
  { sym; ord; map }

let create (binds : (string * Expression.value) list) : t =
  let s =
    {
      sym = Counter.create ();
      ord = BatDynArray.create ();
      map = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
    }
  in
  init s binds;
  s

let add (s : t) (x : name) (v : Num.t) : unit =
  BatDynArray.add s.ord x;
  Hashtbl.replace s.map x v

let find (s : t) (x : name) : Num.t = Hashtbl.find s.map x
let find_opt (s : t) (x : name) : Num.t option = Hashtbl.find_opt s.map x
let exists (s : t) (x : name) : bool = BatDynArray.mem x s.ord

let get (s : t) (x : name) (ty : expr_type) (b : bool) : Num.t =
  let v =
    match find_opt s x with
    | Some v -> v
    | None -> (
        match ty with
        | `I32Type -> I32 (Int32.of_int (Random.int (if b then 2 else 127)))
        | `I64Type -> I64 (Int64.of_int (Random.int 127))
        | `F32Type -> F32 (Int32.bits_of_float (Random.float 127.0))
        | `F64Type -> F64 (Int64.bits_of_float (Random.float 127.0))
        | _ -> assert false)
  in
  add s x v;
  v

let next (s : t) (x : name) : name =
  let id = Counter.get_and_inc s.sym x in
  if id = 0 then x else x ^ "_" ^ string_of_int id

let is_empty (s : t) : bool = 0 = Hashtbl.length s.map

let update (s : t) (binds : (string * Expression.value) list) : unit =
  List.iter
    (fun (x, v) ->
      match v with Num n -> Hashtbl.replace s.map x n | _ -> assert false)
    binds

let to_json (s : t) : string =
  let jsonify_bind (b : bind) : string =
    let n, v = b in
    "{" ^ "\"name\" : \"" ^ n ^ "\", " ^ "\"value\" : \"" ^ Num.string_of_num v
    ^ "\", " ^ "\"type\" : \""
    ^ Types.string_of_num_type (Types.type_of_num v)
    ^ "\"" ^ "}"
  in
  "["
  ^ String.concat ","
      (BatDynArray.fold_left
         (fun a x -> jsonify_bind (x, find s x) :: a)
         [] s.ord)
  ^ "]"

let strings_to_json string_env : string =
  let jsonify_bind b : string =
    let t, x, v = b in
    "{" ^ "\"name\" : \"" ^ x ^ "\", " ^ "\"value\" : \"" ^ v ^ "\", "
    ^ "\"type\" : \"" ^ t ^ "\"" ^ "}"
  in
  "[" ^ String.concat ", " (List.map jsonify_bind string_env) ^ "]"

let to_string (s : t) : string =
  BatDynArray.fold_left
    (fun a k ->
      let v = find s k in
      a ^ "(" ^ k ^ "->" ^ Num.string_of_num v ^ ")\n")
    "" s.ord

let get_key_types (s : t) : (string * expr_type) list =
  Hashtbl.fold (fun k v acc -> (k, Types.type_of_num v) :: acc) s.map []

let to_expr (s : t) : expr list =
  Hashtbl.fold
    (fun k (n : Num.t) acc ->
      let e =
        match n with
        | I32 _ -> Relop (I32 I32.Eq, Symbolic (`I32Type, k), Val (Num n))
        | I64 _ -> Relop (I64 I64.Eq, Symbolic (`I64Type, k), Val (Num n))
        | F32 _ -> Relop (F32 F32.Eq, Symbolic (`F32Type, k), Val (Num n))
        | F64 _ -> Relop (F64 F64.Eq, Symbolic (`F64Type, k), Val (Num n))
      in
      e :: acc)
    s.map []

let int64_of_value (v : Num.t) : int64 =
  match v with I32 i | F32 i -> Int64.of_int32 i | I64 i | F64 i -> i

let rec eval (env : t) (e : expr) : Num.t =
  match simplify e with
  | SymPtr (b, o) ->
      let b : Num.t = I32 b in
      Eval_numeric.eval_binop (I32 I32.Add) b (eval env o)
  | Val (Num n) -> n
  | Binop (op, e1, e2) ->
      let v1 = eval env e1 and v2 = eval env e2 in
      Eval_numeric.eval_binop op v1 v2
  | Unop (op, e') ->
      let v = eval env e' in
      Eval_numeric.eval_unop op v
  | Relop (op, e1, e2) ->
      let v1 = eval env e1 and v2 = eval env e2 in
      Num.num_of_bool (Eval_numeric.eval_relop op v1 v2)
  | Cvtop (op, e') ->
      let v = eval env e' in
      Eval_numeric.eval_cvtop op v
  | Symbolic (ty, var) -> get env var ty false
  | Extract (e', h, l) ->
      let v = int64_of_value (eval env e') in
      I64 (nland64 (Int64.shift_right v (l * 8)) (h - l))
  | Concat (e1, e2) -> (
      let v1 = int64_of_value (eval env e1)
      and v2 = int64_of_value (eval env e2) in
      match (e1, e2) with
      | Extract (_, h1, l1), Extract (_, h2, l2) ->
          let i =
            Int64.(logor (shift_left v1 (l1 * 8)) (shift_left v2 (l2 * 8)))
          in
          if h1 - l2 + (h2 - l2) = 4 then I32 (Int64.to_int32 i) else I64 i
      | Extract (_, h, l), Concat _ ->
          I64 Int64.(logor (shift_left v1 (l * 8)) v2)
      | _ -> assert false)
  | Val _ -> assert false
