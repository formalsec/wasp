open Types
open Values
open Symvalue

type name = string
type bind = name * value

type logicenv = (name, value) Hashtbl.t
type t = logicenv

let order : (name list) ref = ref []

let clear (env : logicenv) : unit =
  order := [];
  Hashtbl.clear env

let init (env : logicenv) (binds : bind list) : unit =
  List.iter (fun (k, v) -> Hashtbl.add env k v) binds

let create (binds : bind list) : logicenv = 
  let env = Hashtbl.create 512 in
  init env binds;
  env

let add (env : logicenv) (k : name) (v : value) : unit =
  order := k :: !order;
  Hashtbl.replace env k v

let find (env : logicenv) (k : name) : value = 
  Hashtbl.find env k

let exists (env : logicenv) (x : name) : bool =
  Hashtbl.mem env x

let is_empty (env : logicenv) : bool =
  0 = (Hashtbl.length env)

let update (env : logicenv) (binds : bind list) : unit =
  List.iter (fun (x, v) -> Hashtbl.replace env x v) binds

let to_list (env : logicenv) : (bind list) =
  List.map (fun x -> (x, find env x)) (List.rev !order)

let to_json (env : bind list) : string =
  let jsonify_bind (b : bind) : string =
    let (n, v) = b in
    "{" ^
        "\"name\" : \"" ^ n ^ "\", " ^
        "\"value\" : \"" ^ (pp_string_of_value v) ^ "\", " ^
        "\"type\" : \"" ^ (string_of_value_type (Values.type_of v)) ^ "\"" ^
    "}"
  in
  "[" ^ (String.concat ", " (List.map jsonify_bind env)) ^ "]"

let to_string (env : logicenv) : string = 
  List.fold_left (fun a b ->
    let (k, v) = b in
    a ^ "(" ^ k ^ "->" ^ (string_of_value v) ^ ")\n"
  ) "" (to_list env)

let get_vars_by_type (t : value_type) (env : logicenv) : string list =
  Hashtbl.fold (fun k v acc ->
    if (Values.type_of v) = t then k :: acc else acc
  ) env []

let to_expr (env : logicenv) : sym_expr list =
  Hashtbl.fold (fun k v acc ->
    let e = match v with
      | I32 _ -> I32Relop (Si32.I32Eq, Symbolic (SymInt32  , k), Value v)
      | I64 _ -> I64Relop (Si64.I64Eq, Symbolic (SymInt64  , k), Value v)
      | F32 _ -> F32Relop (Sf32.F32Eq, Symbolic (SymFloat32, k), Value v)
      | F64 _ -> F64Relop (Sf64.F64Eq, Symbolic (SymFloat64, k), Value v)
    in e :: acc) env []
  
