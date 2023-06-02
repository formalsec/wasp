open Encoding

module type M = sig

    type   t    

    val init : unit -> t
    val store : t -> Expression.t -> Expression.t -> Expression.t -> unit
    val load : t -> Expression.t -> Expression.t -> Expression.t
    val from_heap : Concolic.Heap.t -> t
    val clone : t -> t * t
    val to_string : t -> string
    val to_heap : t -> (Expression.t -> Num.t) -> Concolic.Heap.t
    val alloc : t -> Expression.t -> unit
    val free : t -> Expression.t -> unit
    val in_bounds : t -> Expression.t -> Expression.t -> Expression.t list -> bool

end