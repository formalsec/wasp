type label = string
type condition = string

type history = (label, condition) Hashtbl.t
type t = history

let create () : t =
  let env : t = Hashtbl.create 512 in
  env

let add (hist : t) (lbl : label) (c : condition) : unit =
  Hashtbl.add hist lbl c

let reset (hist : t) : unit =
  Hashtbl.clear hist

let find (hist : t) (lbl : label) : condition =
  Hashtbl.find hist lbl

let mem (hist : t) (lbl : label) : bool =
  Hashtbl.mem hist lbl
