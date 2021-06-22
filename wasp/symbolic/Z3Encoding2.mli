open Z3
open Values

val check_sat_core : Formula.t -> Model.model option
val lift_z3_model : 
  Model.model -> string list -> string list -> string list ->
    string list -> (string  * value) list
