open Values
open Instance

exception Link of Source.region * string
exception Trap of Source.region * string
exception Crash of Source.region * string
exception Exhaustion of Source.region * string

val eval_const : module_inst -> Ast.const -> value
val init : Ast.module_ -> extern list -> module_inst (* raises Link, Trap *)
val invoke : func_inst -> value list -> value list (* raises Trap *)
