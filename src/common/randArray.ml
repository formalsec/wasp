type 'a t = 'a BatDynArray.t

exception Empty

let create () = BatDynArray.create ()
let is_empty a = BatDynArray.empty a
let push v a = BatDynArray.add a v
let add_seq (a : 'a t) (s : 'a Seq.t) : unit = Seq.iter (fun v -> push v a) s
let length = BatDynArray.length

let pop (a : 'a t) : 'a =
  let length = BatDynArray.length a in
  let i = Random.int length in
  let v = BatDynArray.get a i in
  BatDynArray.set a i (BatDynArray.last a);
  BatDynArray.delete_last a;
  v
