open Common
open Encoding
open Types

type typemap = (string, expr_type) Hashtbl.t
type varmap = { sym : Counter.t; ord : string BatDynArray.t; typemap : typemap }
type t = varmap

let create () : t =
  {
    sym = Counter.create ();
    ord = BatDynArray.create ();
    typemap = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
  }

let next (varmap : t) (x : string) : string =
  let id = Counter.get_and_inc varmap.sym x in
  if id = 0 then x else x ^ "_" ^ string_of_int id

let get_vars_by_type (t : expr_type) (varmap : t) : string list =
  Hashtbl.fold
    (fun k v acc -> if v = t then k :: acc else acc)
    varmap.typemap []

let binds (varmap : t) : (string * expr_type) list =
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) varmap.typemap []

let copy (varmap : t) : t =
  let sym = Counter.copy varmap.sym
  and ord = BatDynArray.copy varmap.ord
  and typemap = Hashtbl.copy varmap.typemap in
  { sym; ord; typemap }

let add (varmap : t) (name : string) (ty : expr_type) : unit =
  BatDynArray.add varmap.ord name;
  Hashtbl.replace varmap.typemap name ty
