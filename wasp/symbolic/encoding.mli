open Z3
open Values

val interrupt_z3 : unit -> unit
val check : Formula.t list -> Model.model option

val lift :
  Model.model -> (string * Types.value_type) list -> (string * value) list
