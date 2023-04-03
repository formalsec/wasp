type t = (int32, int32) Hashtbl.t

let replace (ct : t) (address : int32) (size : int32) =
  Hashtbl.replace ct address size

let copy (ct : t) =
  Hashtbl.copy ct

let create () =
  Hashtbl.create Interpreter.Flags.hashtbl_default_size

let find (ct : t) (low : int32) =
  Hashtbl.find ct low

let mem (ct : t) (base : int32) =
  Hashtbl.mem ct base

let remove (ct : t) (base : int32) =
  Hashtbl.remove ct base

