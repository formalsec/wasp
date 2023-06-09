open Encoding
open Types

module type M = sig

    type t

    exception Bounds

    val init : unit -> t
    val store : t -> int32 -> Expression.t -> int32 -> Expression.t -> Expression.t list -> unit
    val load : t -> int32 -> Expression.t -> int32 -> num_type -> Expression.t
    val from_heap : Concolic.Heap.t -> t
    val clone : t -> t * t
    val to_string : t -> string
    val to_heap : t -> (Expression.t -> Num.t) -> Concolic.Heap.t
    val alloc : t -> int32 -> Expression.t -> unit
    val free : t -> int32 -> unit
    val in_bounds : t -> int32 -> Expression.t -> Expression.t
    val check_bound : t -> int32 -> bool
end