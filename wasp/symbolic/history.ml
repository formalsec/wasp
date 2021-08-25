open Symvalue

type id = int32
type path = (id * sym_value) list

type history = string list
type t = history

let history : t ref    = ref []
let current : path ref = ref []

let add (i : id) (v : sym_value) : unit =
  current := (i, v) :: !current

let reset () : unit =
  current := []

let string_of_path (p : path ref) : string =
  List.fold_left (
    fun a (id, (ci, si)) ->
      let b = if ci = Values.(default_value (type_of ci)) then 0 else 1 in
      a ^ (Int32.to_string id) ^ (string_of_int b)
  ) "" !p

let commit () : bool =
  let current_s = (string_of_path current) in
  if List.mem current_s !history then false
  else (
    history := current_s :: !history;
    true
  )
