open Symvalue

type id = int32
type path = (id * sym_value) list

type history = string list
type t = history

let hist : t ref = ref []

let add_record (p : path ref) (i : id) (v : sym_value) : unit =
  p := (i, v) :: !p

let clear_path (p : path ref) : unit =
  p := []

let string_of_path (p : path ref) : string =
  List.fold_left (
    fun a (id, (ci, si)) ->
      let b = if ci = Values.(default_value (type_of ci)) then 0 else 1 in
      a ^ (Int32.to_string id) ^ (string_of_int b)
  ) "" !p

let add_path (p : path ref) : bool =
  let path_s = string_of_path p in
  if List.mem path_s !hist then false
  else (
    hist := path_s :: !hist;
    true
  )
