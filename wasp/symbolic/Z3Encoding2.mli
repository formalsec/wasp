open Z3
open Values

val interrupt_z3 : unit -> unit
val check_sat_core : Formula.t list -> Model.model option
val lift_z3_model : 
  Model.model -> string list -> string list -> string list ->
    string list -> (string  * value) list
