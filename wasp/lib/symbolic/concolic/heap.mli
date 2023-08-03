open Encoding
open Types
open Interpreter.Memory

type memory
type t
type size = int32
type address = int64
type offset = int32
type store = int * Expression.t

exception Bounds
exception InvalidAddress of address

val packed_size : pack_size -> int
val alloc : int -> t
val size : t -> int
val memcpy : t -> t
val clone : t -> t * t
val add_seq : t -> (address * store) Seq.t -> unit
val to_seq : t -> (address * store) Seq.t
val update : t -> Store.t -> unit
val to_list : t -> (address * store) list
val to_string : t -> string
val load_byte : t -> address -> store
val store_byte : t -> address -> store -> unit
val load_string : t -> address -> string
val load_bytes : t -> address -> int -> string * Expression.t
val store_bytes : t -> address -> string -> unit
val load_value : t -> address -> offset -> num_type -> Num.t * Expression.t
val store_value : t -> address -> offset -> Num.t * Expression.t -> unit

val load_packed :
  pack_size ->
  extension ->
  t ->
  address ->
  offset ->
  num_type ->
  Num.t * Expression.t

val store_packed :
  pack_size -> t -> address -> offset -> Num.t * Expression.t -> unit
