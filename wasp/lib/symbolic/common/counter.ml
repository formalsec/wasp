type name = string
type count = int
type counter = (name, count) Hashtbl.t
type t = counter

let create () : counter = Hashtbl.create Interpreter.Flags.hashtbl_default_size
let clear (cnt : counter) : unit = Hashtbl.clear cnt
let copy (cnt : t) : t = Hashtbl.copy cnt

let reset (cnt : counter) : unit =
  Seq.iter (fun (k, _) -> Hashtbl.replace cnt k 0) (Hashtbl.to_seq cnt)

let add (cnt : counter) (key : name) (data : count) : unit =
  Hashtbl.replace cnt key data

let find (cnt : counter) (x : name) : count = Hashtbl.find cnt x

let get_and_inc (cnt : counter) (x : name) : count =
  let c = try find cnt x with Not_found -> 0 in
  add cnt x (c + 1);
  c

let exists (cnt : counter) (x : name) : bool = Hashtbl.mem cnt x

let replace (cnt : counter) (key : name) (data : count) : unit =
  Hashtbl.replace cnt key data

let to_string (cnt : counter) : string =
  Seq.fold_left
    (fun a b ->
      let k, c = b in
      a ^ "(" ^ k ^ "-> cnt=" ^ string_of_int c ^ ")\n")
    "" (Hashtbl.to_seq cnt)
