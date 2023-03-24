open Common
open Encoding
open Types

type varmap = (string, num_type) Hashtbl.t
type t = varmap

let symbols = Counter.create ()

let next (x : string) : string =
  let id = Counter.get_and_inc symbols x in
  if id = 0 then x else x ^ "_" ^ string_of_int id

let get_vars_by_type (t : num_type) (varmap : t) : string list =
  Hashtbl.fold (fun k v acc ->
    if v = t then k :: acc else acc
  ) varmap []

let binds (varmap : t) : (string * num_type) list =
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) varmap []
