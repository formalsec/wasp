open Syntax.Val

type globals = (int32, sym_value) Hashtbl.t
type t = globals

let create () = Hashtbl.create Interpreter.Flags.hashtbl_default_size
let reset g = Hashtbl.reset g
let clear g = Hashtbl.clear g
let add_seq g binds = Hashtbl.add_seq g binds
let copy g = Hashtbl.copy g
let add g i v = Hashtbl.replace g i v
let find g i = Hashtbl.find g i
let exists g i = Hashtbl.mem g i
let to_seq g = Hashtbl.to_seq g
