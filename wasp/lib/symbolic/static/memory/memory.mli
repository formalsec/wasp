open Common
open Bug
open Encoding
open Types
open Interpreter.Memory

type size = int32
type address = int64
type offset = int32

module type SymbolicMemory = sig
  type t
  type e
  exception Bounds

  val from_heap : Concolic.Heap.t -> t

  val clone : t -> t * t

  val load_value : 
    e -> Varmap.t -> t -> Expression.t -> offset -> num_type -> 
    ((t * Expression.t * Expression.t list) list, bug) result

  val load_packed :
    e -> Varmap.t -> pack_size -> t -> Expression.t -> 
    offset -> num_type -> ((t * Expression.t * Expression.t list) list, bug) result

  val load_string : t -> address -> string

  val store_value : 
    e -> Varmap.t -> t -> Expression.t -> offset -> Expression.t -> 
        ((t * Expression.t list) list, bug) result

  val store_packed : 
    e -> Varmap.t -> pack_size -> t -> Expression.t -> offset -> Expression.t -> 
        ((t * Expression.t list) list, bug) result

  val to_string : t -> string

  val to_heap :
    t -> (Expression.t -> Num.t) -> Concolic.Heap.t * (int32, int32) Hashtbl.t

  (*TODO : change int32 to address (int64)*)
  val alloc : 
    e -> Varmap.t -> t -> Expression.t -> Expression.t -> 
      (t * int32 * Expression.t list) list 

  val free : t -> int32 -> (unit, bug) result

  val check_access : t -> Expression.t -> Num.t -> offset -> bug option

  val check_bound : t -> int32 -> bool
end

module type FSMem = functor (E : Common.Encoder) -> SymbolicMemory with type e = E.t


module LazySMem : FSMem
module MapSMem : FSMem
module TreeSMem : FSMem


module ArrayConcrSMem : FSMem
module ArrayForkSMem : FSMem
module ArrayITESMem : FSMem
module OpListSMem : FSMem

module Varmap = Varmap