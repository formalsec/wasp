open Encoding

module type M = sig

    type t

    exception Bounds

    val init : unit -> t
    val store : t -> int32 -> Expression.t -> int32 -> Expression.t -> int -> unit
    val load : (Expression.t -> bool) -> t -> int32 -> Expression.t -> int32 -> int -> Expression.t
    val from_heap : Concolic.Heap.t -> t
    val clone : t -> t * t
    val to_string : t -> string
    val to_heap : t -> (Expression.t -> Num.t) -> Concolic.Heap.t
    val alloc : t -> int32 -> Expression.t -> unit
    val free : t -> int32 -> unit
    val in_bounds : t -> int32 -> Expression.t -> int32 -> int -> Expression.t
    val check_bound : t -> int32 -> bool
end