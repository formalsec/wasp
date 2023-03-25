open Encoding
open Types
open Expression
open Interpreter.Memory

type memory
type t = memory
type size = int32
type address = int64
type offset = int32
type store = int * Expression.t

exception Bounds
exception InvalidAddress of address

val packed_size : pack_size -> int
val alloc : int -> memory
val size : memory -> int
val clear : memory -> unit
val memcpy : memory -> memory
val add_seq : memory -> (address * store) Seq.t -> unit
val to_seq : memory -> (address * store) Seq.t
val update : memory -> Store.t -> unit
val to_list : memory -> (address * store) list
val to_string : memory -> string
val load_byte : memory -> address -> store
val store_byte : memory -> address -> store -> unit
val load_string : memory -> address -> string
val load_bytes : memory -> address -> int -> string * Expression.t
val store_bytes : memory -> address -> string -> unit
val load_value : memory -> address -> offset -> num_type -> value
val store_value : memory -> address -> offset -> value -> unit

val load_packed :
  pack_size -> extension -> memory -> address -> offset -> num_type -> value

val store_packed : pack_size -> memory -> address -> offset -> value -> unit
