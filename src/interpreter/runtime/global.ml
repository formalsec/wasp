open Types
open Values

type global =
  { mutable content : value
  ; mut : mutability
  }

type t = global

exception Type

exception NotMutable

let alloc (GlobalType (t, mut)) v =
  if type_of v <> t then raise Type;
  { content = v; mut }

let type_of glob = GlobalType (type_of glob.content, glob.mut)

let load glob = glob.content

let store glob v =
  if glob.mut <> Mutable then raise NotMutable;
  if Values.type_of v <> Values.type_of glob.content then raise Type;
  glob.content <- v

let safe_store glob v = if glob.mut = Mutable then glob.content <- v

let globcpy (glob : global) : global = alloc (type_of glob) glob.content

let contents (globs : global list) : value list =
  let rec loop acc = function [] -> acc | h :: t -> loop (load h :: acc) t in
  List.rev (loop [] globs)
