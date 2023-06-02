open Encoding


module MapMemory : Block.M = struct
  type size = Expression.t
  type address = int

  type op = Expression.t * Expression.t * Expression.t list(* path condition?*)
  type t = { map : (address, size * op list) Hashtbl.t; mutable next : int }


  let init () : t = { map = Hashtbl.create Interpreter.Flags.hashtbl_default_size; next = 0 }

  let to_string (h : t) : string =
    Hashtbl.fold
    (fun k (sz, ops) accum -> 
      accum 
      ^ Int.to_string k
      ^ " -> ("
      ^ Expression.to_string sz
      ^ ", " ^ "["
      ^ String.concat ", "
          (List.map
             (fun (i, v, _) ->
               Expression.to_string i
               ^ " "
               ^ Expression.to_string v)
             ops)
      ^ "]" ^ ")")
    h.map ""

  let store (h : t) (addr : Expression.t) (idx : Expression.t) (b : Expression.t) =
    failwith "not implemented"

  let load (h : t) (addr : Expression.t) (idx : Expression.t) : Expression.t =
    failwith "not implemented"

  let from_heap (h : Concolic.Heap.t) : t =
    failwith "not implemented"


  let clone (h : t) : t * t = 
    failwith "not implemented"


  let to_heap (h : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t =
    failwith "not implemented"


  let alloc (h : t) (sz : Expression.t) : unit =
    let next = h.next in
    Hashtbl.add h.map next (sz, []);
    h.next <- h.next + 1

  let free (h : t) (a : Expression.t) : unit =
    failwith "not implemented"

  let in_bounds (h : t) (block : Expression.t) (index : Expression.t) (pc : Expression.t list) : bool =
    failwith "not implemented"

end