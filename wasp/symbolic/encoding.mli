open Z3
open Values
open Symvalue

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
val value_binds : t -> (string * Types.value_type) list -> (string * value) list

val string_binds :
  t -> (string * Types.value_type) list -> (string * string * string) list