open Types
open Values
open Symvalue

type name = string
type bind = name * value

type logicenv = (name, value) Hashtbl.t
type t = logicenv

let create (binds : bind list) : logicenv = 
  let env = Hashtbl.create 512 in
  List.iter (fun (k, v) -> Hashtbl.add env k v) binds;
  env

let clear (env : logicenv) : unit =
  Hashtbl.clear env

let init (env : logicenv) (binds : bind list) : unit =
  List.iter (fun (k, v) -> Hashtbl.add env k v) binds

let add (env : logicenv) (k : name) (v : value) : unit =
  Hashtbl.replace env k v

let find (env : logicenv) (k : name) : value = 
  Hashtbl.find env k

let exists (env : logicenv) (x : name) : bool =
  Hashtbl.mem env x

let is_empty (env : logicenv) : bool =
  0 = (Hashtbl.length env)

let to_json (env : bind list) : string =
  let jsonify_bind (b : bind) : string =
    let (n, v) = b in
    "\"" ^ n ^ "\" : \"" ^ (string_of_value v) ^ "\""
  in
  let rec loop acc = function
    | [] -> "}"
    | a :: [] -> 
        if acc = "{" then ("{" ^ (jsonify_bind a) ^ "}")
                     else (acc ^ ", " ^ (jsonify_bind a) ^ "}")
    | a :: b :: t -> 
        let acc = if acc = "{" then (acc ^ (jsonify_bind a))
                               else (acc ^ ", " ^ (jsonify_bind a))
        in loop acc (b :: t)
  in loop "{" env

let to_string (env : logicenv) : string = 
  Seq.fold_left (fun a b ->
    let (k, v) = b in
    a ^ "(" ^ k ^ "->" ^ (string_of_value v) ^ ")\n"
  ) "" (Hashtbl.to_seq env)

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
  
