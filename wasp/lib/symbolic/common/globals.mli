type 'a globals
type 'a t = 'a globals

val create : unit -> 'a t
val copy : 'a t -> 'a t
val add : 'a t -> int32 -> 'a -> unit
val find : 'a t -> int32 -> 'a
val of_seq : (int32 * 'a) Seq.t -> 'a t
val convert : 'a t -> ('a -> 'b) -> 'b t
