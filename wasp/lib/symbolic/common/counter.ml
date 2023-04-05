type count = int
type 'a t = ('a, count) Hashtbl.t

let create () : 'a t = Hashtbl.create Interpreter.Flags.hashtbl_default_size
let clear (cnt : 'a t) : unit = Hashtbl.clear cnt
let copy (cnt : 'a t) : 'a t = Hashtbl.copy cnt

let reset (cnt : 'a t) : unit =
  Seq.iter (fun (k, _) -> Hashtbl.replace cnt k 0) (Hashtbl.to_seq cnt)

let add (cnt : 'a t) (key : 'a) (data : count) : unit =
  Hashtbl.replace cnt key data

let find (cnt : 'a t) (x : 'a) : count = Hashtbl.find cnt x

let get_and_inc (cnt : 'a t) (x : 'a) : count =
  let c = try find cnt x with Not_found -> 0 in
  add cnt x (c + 1);
  c

let exists (cnt : 'a t) (x : 'a) : bool = Hashtbl.mem cnt x

let replace (cnt : 'a t) (key : 'a) (data : count) : unit =
  Hashtbl.replace cnt key data

let to_string (cnt : 'a t) : string =
  Seq.fold_left
    (fun a b ->
      let k, c = b in
      a ^ "(" ^ k ^ "-> cnt=" ^ string_of_int c ^ ")\n")
    "" (Hashtbl.to_seq cnt)
