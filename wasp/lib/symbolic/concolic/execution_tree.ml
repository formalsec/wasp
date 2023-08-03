type 'a t = Leaf | Node of 'a parent * 'a option * 'a left * 'a right
and 'a parent = 'a t ref option
and 'a left = 'a t ref
and 'a right = 'a t ref

exception Invalid_branch

let is_leaf (t : 'a t ref) : bool = match !t with Leaf -> true | _ -> false
let is_node (t : 'a t ref) : bool = not (is_leaf t)

let can_branch (t : 'a t ref) : bool =
  match !t with
  | Leaf -> true
  | Node (_, _, l, r) -> (
      match (!l, !r) with Leaf, Leaf -> true | _ -> false)

let rec update_node (t : 'a t ref) (v : 'a) : unit =
  match !t with
  | Leaf -> ()
  | Node (p, _, l, r) ->
      update_node l v;
      update_node r v;
      t := Node (p, Some v, l, r)

let find (t : 'a t ref) : 'a option =
  match !t with Leaf -> None | Node (_, v, _, _) -> v

let move_true (t : 'a t ref) : 'a left * bool =
  match !t with
  | Leaf ->
      let l = ref (Node (Some t, None, ref Leaf, ref Leaf))
      and r = ref (Node (Some t, None, ref Leaf, ref Leaf)) in
      t := Node (None, None, l, r);
      (l, true)
  | Node (parent, v, l, r) ->
      let b = can_branch t in
      if is_leaf l then l := Node (Some t, v, ref Leaf, ref Leaf);
      (l, b)

let move_false (t : 'a t ref) : 'a right * bool =
  match !t with
  | Leaf ->
      let l = ref (Node (Some t, None, ref Leaf, ref Leaf))
      and r = ref (Node (Some t, None, ref Leaf, ref Leaf)) in
      t := Node (None, None, l, r);
      (r, true)
  | Node (parent, v, l, r) ->
      let b = can_branch t in
      if is_leaf r then r := Node (Some t, v, ref Leaf, ref Leaf);
      (r, b)
