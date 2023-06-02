open Encoding
open Value
open Expression
open Types
open Memory

type size = int32
type address = int64
type offset = int32

module MapMemory : MemoryBackend = struct

  type addr = int
  type size = Expression.t
  type op = Expression.t * Expression.t * Expression.t list(* path condition?*)
  type t = { map : (addr, size * op list) Hashtbl.t; mutable next : int }
  type vt = Expression.t

  let store_byte (h : t) (a : address) (b : Expression.t) =
    failwith "not implemented"

  let load_byte (h : t) (a : address) : Expression.t =
    failwith "not implemented"

  let from_heap (h : Concolic.Heap.t) : t =
    failwith "not implemented"

  let clone (h : t) : t * t = 
    failwith "not implemented"

  let to_string (h : t) : string =
    Hashtbl.fold
    (fun k (sz, ops) accum -> 
      accum 
      ^ Int.to_string k
      ^ " -> ("
      ^ Expression.to_string sz
      ^ ", " ^ "["
      ^ String.concat ", "
          (List.map
             (fun (i, v, _) ->
               Expression.to_string i
               ^ " "
               ^ Expression.to_string v)
             ops)
      ^ "]" ^ ")")
    h.map ""

  let to_heap (h : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t =
    failwith "not implemented"

  exception Bounds
end