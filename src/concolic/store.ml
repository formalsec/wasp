open Common
open Smtml

type name = string

type bind = name * Num.t

type store =
  { sym : name Counter.t
  ; ord : name Stack.t
  ; map : (name, Num.t) Hashtbl.t
  }

type t = store

let reset (s : t) : unit =
  Counter.clear s.sym;
  Hashtbl.clear s.map;
  Stack.clear s.ord

let copy (s : t) : t =
  let sym = Counter.copy s.sym
  and ord = Stack.copy s.ord
  and map = Hashtbl.copy s.map in
  { sym; ord; map }

let clear (s : t) : unit = Hashtbl.clear s.map

let init (s : t) (binds : (Symbol.t * Value.t) list) : unit =
  List.iter
    (fun (x, v) ->
      match v with
      | Value.Num n -> Hashtbl.replace s.map (Symbol.to_string x) n
      | _ -> assert false )
    binds

let from_parts (sym : name Counter.t) (ord : name Stack.t)
  (map : (name, Num.t) Hashtbl.t) : t =
  { sym; ord; map }

let create (binds : (Symbol.t * Value.t) list) : t =
  let s =
    { sym = Counter.create ()
    ; ord = Stack.create ()
    ; map = Hashtbl.create Interpreter.Flags.hashtbl_default_size
    }
  in
  init s binds;
  s

let add (s : t) (x : name) (v : Num.t) : unit =
  Stack.push x s.ord;
  Hashtbl.replace s.map x v

let find (s : t) (x : name) : Num.t = Hashtbl.find s.map x

let find_opt (s : t) (x : name) : Num.t option = Hashtbl.find_opt s.map x

let exists (s : t) (x : name) : bool = Hashtbl.mem s.map x

let get (s : t) (x : name) (ty : Ty.t) (b : bool) : Num.t =
  let v =
    match find_opt s x with
    | Some v -> v
    | None -> (
      match ty with
      | Ty.Ty_bitv 32 ->
        Num.I32 (Int32.of_int (Random.int (if b then 2 else 127)))
      | Ty.Ty_bitv 64 -> Num.I64 (Int64.of_int (Random.int 127))
      | Ty.Ty_fp 32 -> Num.F32 (Int32.bits_of_float (Random.float 127.0))
      | Ty.Ty_fp 64 -> Num.F64 (Int64.bits_of_float (Random.float 127.0))
      | _ -> assert false )
  in
  add s x v;
  v

let next (s : t) (x : name) : name =
  let id = Counter.get_and_inc s.sym x in
  if id = 0 then x else x ^ "_" ^ string_of_int id

let is_empty (s : t) : bool = 0 = Hashtbl.length s.map

let update (s : t) (binds : (Symbol.t * Value.t) list) : unit =
  List.iter
    (fun (x, v) ->
      match v with
      | Value.Num n -> Hashtbl.replace s.map (Symbol.to_string x) n
      | _ -> assert false )
    binds

let to_json (s : t) : string =
  let jsonify_bind (b : bind) : string =
    let n, v = b in
    "{" ^ "\"name\" : \"" ^ n ^ "\", " ^ "\"value\" : \"" ^ Num.to_string v
    ^ "\", " ^ "\"type\" : \""
    ^ Ty.string_of_type (Num.type_of v)
    ^ "\"" ^ "}"
  in
  "["
  ^ String.concat ","
      (Seq.fold_left
         (fun a x -> jsonify_bind (x, find s x) :: a)
         [] (Stack.to_seq s.ord) )
  ^ "]"

let strings_to_json string_env : string =
  let jsonify_bind b : string =
    let t, x, v = b in
    "{" ^ "\"name\" : \"" ^ x ^ "\", " ^ "\"value\" : \"" ^ v ^ "\", "
    ^ "\"type\" : \"" ^ t ^ "\"" ^ "}"
  in
  "[" ^ String.concat ", " (List.map jsonify_bind string_env) ^ "]"

let to_string (s : t) : string =
  Seq.fold_left
    (fun a k ->
      let v = find s k in
      a ^ "(" ^ k ^ "->" ^ Num.to_string v ^ ")\n" )
    "" (Stack.to_seq s.ord)

let get_key_types (s : t) : Symbol.t list =
  Hashtbl.fold (fun k v acc -> Symbol.make (Num.type_of v) k :: acc) s.map []

let to_expr (s : t) : Expr.t list =
  Hashtbl.fold
    (fun k (n : Num.t) acc ->
      let e =
        match n with
        | Num.I32 _ ->
          let sym = Expr.symbol (Symbol.make (Ty.Ty_bitv 32) k) in
          Expr.(relop Ty.Ty_bool Ty.Eq sym (value (Value.Num n)))
        | Num.I64 _ ->
          let sym = Expr.symbol (Symbol.make (Ty.Ty_bitv 64) k) in
          Expr.(relop Ty.Ty_bool Ty.Eq sym (value (Value.Num n)))
        | Num.F32 _ ->
          let sym = Expr.symbol (Symbol.make (Ty.Ty_fp 32) k) in
          Expr.(relop (Ty.Ty_fp 32) Ty.Eq sym (value (Value.Num n)))
        | Num.F64 _ ->
          let sym = Expr.symbol (Symbol.make (Ty.Ty_fp 64) k) in
          Expr.(relop (Ty.Ty_fp 64) Ty.Eq sym (value (Value.Num n)))
        | _ -> assert false
      in
      e :: acc )
    s.map []

let int64_of_value (v : Value.t) : int64 =
  match v with
  | Num (I32 i | F32 i) -> Int64.of_int32 i
  | Num (I64 i | F64 i) -> i
  | _ -> assert false

let rec eval (env : t) (e : Expr.t) : Value.t =
  let open Ty in
  let open Expr in
  match Expr.(view (simplify e)) with
  | Ptr { base; offset } ->
    let b = Value.Num (Num.I32 base) in
    Smtml.Eval.binop (Ty_bitv 32) Add b (eval env offset)
  | Val (Value.Num _ as v) -> v
  | Binop (ty, op, e1, e2) ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    Smtml.Eval.binop ty op v1 v2
  | Unop (ty, op, e') ->
    let v = eval env e' in
    Smtml.Eval.unop ty op v
  | Relop (ty, op, e1, e2) ->
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    Num (Num.num_of_bool (Smtml.Eval.relop ty op v1 v2))
  | Cvtop (ty, op, e) ->
    let v = eval env e in
    Smtml.Eval.cvtop ty op v
  | Symbol s -> (
    let x = Symbol.to_string s in
    match find_opt env x with
    | Some v -> Num v
    | None ->
      let v : Num.t =
        match Symbol.type_of s with
        | Ty.Ty_bitv 32 -> I32 (Int32.of_int (Random.int 127))
        | Ty.Ty_bitv 64 -> I64 (Int64.of_int (Random.int 127))
        | Ty.Ty_fp 32 -> F32 (Int32.bits_of_float (Random.float 127.0))
        | Ty.Ty_fp 64 -> F64 (Int64.bits_of_float (Random.float 127.0))
        | _ -> assert false
      in
      Hashtbl.replace env.map x v;
      Num v )
  | Extract (e, _, _) ->
    let _v = int64_of_value (eval env e) in
    (* Num (I64 (Expr.nland64 (Int64.shift_right v (l * 8)) (h - l))) *)
    assert false
  | Concat (e1, e2) -> (
    let v1 = int64_of_value (eval env e1) in
    let v2 = int64_of_value (eval env e2) in
    match (Expr.view e1, Expr.view e2) with
    | Extract (_, h1, l1), Extract (_, h2, l2) ->
      let i = Int64.(logor (shift_left v1 (l1 * 8)) (shift_left v2 (l2 * 8))) in
      Num (if h1 - l2 + (h2 - l2) = 4 then I32 (Int64.to_int32 i) else I64 i)
    | Extract (_, _, l), Concat _ ->
      Num (I64 Int64.(logor (shift_left v1 (l * 8)) v2))
    | _ -> assert false )
  | Val _ | Triop _ | List _ | Naryop _ | App _ -> assert false
