open Syntax.Val

type formula =
  | True
  | False
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Relop of sym_expr

type t = formula

val negate : formula -> formula
val conjunct : formula list -> formula
val length : formula -> int
val to_formulas : sym_expr list -> formula list
val to_formula : sym_expr list -> formula
val to_string : formula -> string
val pp_to_string : formula -> string
val get_vars : formula -> (string * symbolic) list
