open Types

type varmap = (string, value_type) Hashtbl.t
type t = varmap

let get_vars_by_type (t : value_type) (varmap : t) : string list =
  Hashtbl.fold (fun k v acc ->
    if v = t then k :: acc else acc
  ) varmap []
