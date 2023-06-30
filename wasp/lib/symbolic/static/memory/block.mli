open Encoding
open Types

module type M = sig

    type t

    exception Bounds

    val init : unit -> t
    val store : t -> int32 -> Expression.t -> int32 -> Expression.t -> int -> (t * Expression.t list) list
    val load : (Expression.t -> bool) -> t -> int32 -> Expression.t -> int32 -> int -> num_type -> bool -> (t * Expression.t * Expression.t list) list
    val from_heap : Concolic.Heap.t -> t
    val clone : t -> t * t
    val to_string : t -> string
    val to_heap : t -> (Expression.t -> Num.t) -> Concolic.Heap.t
    val alloc : t -> int32 -> Expression.t -> (t * int32 * Expression.t list) list
    val free : t -> int32 -> unit
    val in_bounds : t -> int32 -> Expression.t -> int32 -> int -> Expression.t
    val check_bound : t -> int32 -> bool
end