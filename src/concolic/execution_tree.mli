type 'a t = Leaf | Node of 'a parent * 'a option * 'a left * 'a right
and 'a parent = 'a t ref option
and 'a left = 'a t ref
and 'a right = 'a t ref

exception Invalid_branch

val is_leaf : 'a t ref -> bool
val is_node : 'a t ref -> bool
val can_branch : 'a t ref -> bool
val update_node : 'a t ref -> 'a -> unit
val find : 'a t ref -> 'a option
val move_true : 'a t ref -> 'a left * bool
val move_false : 'a t ref -> 'a right * bool
