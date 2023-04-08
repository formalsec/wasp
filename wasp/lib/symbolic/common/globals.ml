type 'a globals = (int32, 'a) Hashtbl.t
type 'a t = 'a globals

let create () = Hashtbl.create Interpreter.Flags.hashtbl_default_size
let copy g = Hashtbl.copy g
let add g i v = Hashtbl.replace g i v
let find g i = Hashtbl.find g i
let to_seq g = Hashtbl.to_seq g

let of_seq (seq : (int32 * 'a) Seq.t) : 'a t =
  let res = create () in
  Hashtbl.add_seq res seq;
  res

let convert (og : 'a t) (conv : 'a -> 'b) : 'b t =
  let og_seq = to_seq og in
  let new_seq = Seq.map (fun (address, v) -> (address, conv v)) og_seq in
  of_seq new_seq
