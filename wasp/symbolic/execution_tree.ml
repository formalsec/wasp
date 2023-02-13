type t = Leaf | Node of t ref * t ref

let move_true (t : t ref) : t ref * bool =
  match !t with
  | Leaf ->
      let rt = ref Leaf and rf = ref Leaf in
      t := Node (rt, rf);
      (rt, true)
  | Node (rt, rf) -> (rt, false)

let move_false (t : t ref) : t ref * bool =
  match !t with
  | Leaf ->
      let rt = ref Leaf and rf = ref Leaf in
      t := Node (rt, rf);
      (rf, true)
  | Node (rt, rf) -> (rf, false)
