open Encoding
open Types
open Interpreter.Memory

type size = int32
type address = int64
type offset = int32

module type MemoryBackend = sig
  type t

  exception Bounds

  val store_byte : t -> address -> Expression.t -> unit
  val load_byte : t -> address -> Expression.t
  val from_heap : Concolic.Heap.t -> t
  val clone : t -> t * t
  val to_string : t -> string
  val to_heap : t -> (Expression.t -> Num.t) -> Concolic.Heap.t
end

module LazyMemory : MemoryBackend
module MapMemory : MemoryBackend
module TreeMemory : MemoryBackend

module type SymbolicMemory = sig
  type t

  exception Bounds

  val from_heap : Concolic.Heap.t -> t
  val clone : t -> t * t
  val load_value : t -> address -> offset -> num_type -> Expression.t

  val load_packed :
    pack_size -> t -> address -> offset -> num_type -> Expression.t

  val load_string : t -> address -> string
  val store_value : t -> address -> offset -> Expression.t -> unit
  val store_packed : pack_size -> t -> address -> offset -> Expression.t -> unit
  val to_string : t -> string
  val to_heap : t -> (Expression.t -> Num.t) -> Concolic.Heap.t
end

module LazySMem : SymbolicMemory
module MapSMem : SymbolicMemory
module TreeSMem : SymbolicMemory
