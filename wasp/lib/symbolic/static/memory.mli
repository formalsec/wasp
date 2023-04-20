open Common
open Bug
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
  val load_value : 
    (Expression.t -> Num.t) -> t -> Expression.t -> offset -> num_type -> 
    ((t * Expression.t * Expression.t list) list, bug) result
  val load_packed :
    (Expression.t -> Num.t) -> pack_size -> t -> Expression.t -> 
      offset -> num_type -> ((t * Expression.t * Expression.t list) list, bug) result

    val load_string : t -> address -> string

    val store_value : 
      (Expression.t -> Num.t) -> t -> Expression.t -> offset -> Expression.t -> 
          ((t * Expression.t list) list, bug) result
    val store_packed : 
      (Expression.t -> Num.t) -> pack_size -> t -> Expression.t -> offset -> Expression.t -> 
          ((t * Expression.t list) list, bug) result
    val to_string : t -> string
  
    val to_heap :
      t -> (Expression.t -> Num.t) -> Concolic.Heap.t * (int32, int32) Hashtbl.t
  
    (*TODO : change int32 to address (int64)*)
    val alloc : t -> int32 -> size -> unit
    val free : t -> int32 -> unit
    val check_access : t -> Expression.t -> Num.t -> offset -> bug option
    val check_bound : t -> int32 -> bool
end

module LazySMem : SymbolicMemory
module MapSMem : SymbolicMemory
module TreeSMem : SymbolicMemory
