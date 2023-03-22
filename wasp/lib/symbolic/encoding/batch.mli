open Z3
open Syntax.Val
open Interpreter.Types
open Interpreter.Values

type t = { solver : s; pc : path_conditions ref }
and s = Solver.solver

val time_solver : float ref
val create : unit -> t
val clone : t -> t
val interrupt : unit -> unit
val add : t -> sym_expr -> unit
val check : t -> sym_expr list -> bool
val fork : t -> sym_expr -> bool * bool
val model : t -> Model.model
val get_model : t -> Model.model

val model_binds :
  Model.model -> (string * value_type) list -> (string * value) list

val value_binds : t -> (string * value_type) list -> (string * value) list

val string_binds :
  t -> (string * value_type) list -> (string * string * string) list
