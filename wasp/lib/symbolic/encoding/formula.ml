open Syntax
open Val

type formula =
  | True
  | False
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Relop of Val.sym_expr

type t = formula

let rec negate (f : formula) : formula =
  match f with
  | True -> False
  | False -> True
  | Not c -> c
  | And (c1, c2) -> Or (negate c1, negate c2)
  | Or (c1, c2) -> And (negate c1, negate c2)
  | Relop e -> Relop (Val.negate_relop e)

let conjunct (conds : formula list) : formula =
  if conds = [] then
    True
  else
    (
    let rec loop (acc : t) = function
      | []     -> acc
      | h :: t -> loop (And (acc, h)) t
    in loop (List.hd conds) (List.tl conds)
  )

let rec to_string_aux (p : Val.sym_expr -> string)
    (f : formula) : string =
  match f with
  | True -> "True"
  | False -> "False"
  | Not c -> "(Not " ^ to_string_aux p c ^ ")"
  | And (c1, c2) ->
      let c1_str = to_string_aux p c1 and c2_str = to_string_aux p c2 in
      "(" ^ c1_str ^ " /\\ " ^ c2_str ^ ")"
  | Or (c1, c2) ->
      let c1_str = to_string_aux p c1 and c2_str = to_string_aux p c2 in
      "(" ^ c1_str ^ " \\/ " ^ c2_str ^ ")"
  | Relop e -> p e

let to_string (f : formula) : string = to_string_aux Val.to_string f
let pp_to_string (f : formula) : string = to_string_aux Val.pp_to_string f

let rec length (e : formula) : int =
  match e with
  | True | False | Relop _ -> 1
  | Not c -> 1 + length c
  | And (c1, c2) -> 1 + length c1 + length c2
  | Or (c1, c2) -> 1 + length c1 + length c2

let to_formulas (pc : sym_expr list) : formula list =
  List.map (fun e -> Relop e) pc

let to_formula (pc : sym_expr list) : formula = conjunct (to_formulas pc)

let rec get_vars (e : formula) : (string * symbolic) list =
  match e with
  | True | False -> []
  | Not c -> get_vars c
  | And (c1, c2) -> get_vars c1 @ get_vars c2
  | Or (c1, c2) -> get_vars c1 @ get_vars c2
  | Relop e -> Val.get_symbols e
