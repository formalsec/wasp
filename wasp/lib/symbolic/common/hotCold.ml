type 'a hot_cold = { mutable hot : 'a BatDeque.t; mutable cold : 'a BatDeque.t }
type 'a t = 'a hot_cold

exception Empty

let hot_max = 64

let create () =
  let hot = BatDeque.empty in
  let cold = BatDeque.empty in
  { hot; cold }

let is_empty a = BatDeque.size a.hot == 0 && BatDeque.size a.cold == 0

let push (v : 'a) (a : 'a t) : unit =
  if BatDeque.size a.hot + 1 < hot_max then
    let new_hot = BatDeque.cons v a.hot in
    a.hot <- new_hot
  else
    let new_cold = BatDeque.cons v a.cold in
    a.cold <- new_cold

let add_seq (a : 'a t) (s : 'a Seq.t) : unit =
  let l = List.of_seq s in
  let l_len = List.length l in
  let push (v : 'a) : unit =
    if BatDeque.size a.hot + l_len < hot_max then
      let new_hot = BatDeque.cons v a.hot in
      a.hot <- new_hot
    else
      let new_cold = BatDeque.cons v a.cold in
      a.cold <- new_cold
  in
  Seq.iter push s

let length (a : 'a t) = BatDeque.size a.hot + BatDeque.size a.cold

let pop (a : 'a t) : 'a =
  match BatDeque.front a.hot with
  | Some (head, tail) ->
      a.hot <- tail;
      head
  | None -> (
      a.hot <- a.cold;
      a.cold <- BatDeque.empty;
      match BatDeque.front a.hot with
      | Some (head, tail) ->
          a.hot <- tail;
          head
      | None -> raise Empty)
