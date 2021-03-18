open Types
open Symvalue

(* TODO(update): refactor using c_sym_value *)
type memory
type t = memory

type size = int32
type address = int64
type offset = int32

(* TODO(create): replace failwith, with proper exceptions *)
exception Bounds

val packed_size : Memory.pack_size -> int

val alloc : int -> memory
val size : memory -> int
val to_string : memory -> string

val load_byte : memory -> address -> int
val store_byte : memory -> address -> int -> unit
val load_bytes : memory -> address -> int -> string
val store_bytes : memory -> address -> string -> unit

val load_value : 
  memory -> address -> offset -> value_type -> c_sym_value
val store_value : 
  memory -> address -> offset -> c_sym_value -> unit
val load_packed : 
  Memory.pack_size -> memory -> address -> offset -> value_type -> c_sym_value
val store_packed : 
  Memory.pack_size -> memory -> address -> offset -> c_sym_value -> unit

(* TODO(update): int conversion in memory module?*)
val effective_address : I64.t -> int32 -> int64

