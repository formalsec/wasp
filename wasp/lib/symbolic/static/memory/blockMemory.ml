open Common
open Bug
open Encoding
open Value
open Expression
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
  val alloc : t -> size -> unit
end


module type SymbolicMemory = sig
  type t

  exception Bounds

  val from_heap : Concolic.Heap.t -> t
  val clone : t -> t * t
  val load_value : 
    (Expression.t -> Num.t) -> t -> Expression.t -> 
      offset -> num_type -> ((t * Expression.t * Expression.t list) list, bug) result 

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
  val alloc : 
    (Expression.t option -> bool) -> (Expression.t -> Num.t) ->
    t -> Expression.t -> Expression.t -> (t * int32 * Expression.t list) list 

  val free : t -> int32 -> (unit, bug) result
  val check_access : t -> Expression.t -> Num.t -> offset -> bug option
  val check_bound : t -> int32 -> bool
end


module SMem (MB : MemoryBackend) : SymbolicMemory = struct
  type t = MB.t

  exception Bounds = MB.Bounds

  (* helper functions *)
  (* let effective_address (a : address) (o : offset) : address =
    let ea = Int64.(add a (of_int32 o)) in
    if Interpreter.I64.lt_u ea a then raise MB.Bounds;
    ea

  let concr_ptr (sym_ptr : Expression.t ) 
    (expr_to_value : (Expression.t -> Num.t)) = 
    let sym_ptr = simplify sym_ptr in
    let ptr =
      match concretize_ptr sym_ptr with
      | Some ptr -> ptr
      | None -> expr_to_value sym_ptr
    in
    let open Interpreter in
    (I64_convert.extend_i32_u
      (Values.I32Value.of_value (Evaluations.to_value ptr)), ptr)

  
  let length_pack_size (sz : pack_size) : int =
    match sz with Pack8 -> 1 | Pack16 -> 2 | Pack32 -> 4

  let storen (mem : MB.t) (a : address) (o : offset) (n : int)
      (value : Expression.t) : unit =
    let rec loop mem a i n x =
      if n > i then (
        MB.store_byte mem a (Expression.Extract (x, i + 1, i));
        loop mem (Int64.add a 1L) (i + 1) n x)
    in
    loop mem (effective_address a o) 0 n value

  let loadn (mem : MB.t) (a : address) (o : offset) (n : int) :
      Expression.t list =
    let rec loop a n acc =
      if n = 0 then acc
      else
        let se = MB.load_byte mem a in
        loop (Int64.sub a 1L) (n - 1) (se :: acc)
    in
    loop Int64.(add (effective_address a o) (of_int (n - 1))) n [] *)

  (* Public functions *)
  let from_heap (h : Concolic.Heap.t) : t =
    let backend = MB.from_heap h in
    backend

  let clone (m : t) : t * t =
    let backend1, backend2 = MB.clone m in
    (backend1, backend2)

  let check_access (m : t) (sym_ptr : Expression.t) (ptr : Num.t) (o : offset) : bug option =
    let base_ptr = concretize_base_ptr sym_ptr in
    ignore base_ptr;
    failwith "not implemented"

  let load_value (expr_to_value : Expression.t -> Num.t) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (ty : num_type) :
    ((t * Expression.t * Expression.t list) list, bug) result =
    failwith "not implemented"

  let load_packed (expr_to_value : Expression.t -> Num.t) (sz : pack_size) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (ty : num_type) :
    ((t * Expression.t * Expression.t list) list, bug) result =
    failwith "not implemented"

  let load_string (mem : t) (a : address) : string =
    let rec loop a acc =
      let sb = MB.load_byte mem a in
      let b =
        match sb with
        | Extract (Val (Num (I64 b)), 1, 0) -> Int64.to_int b
        | _ ->
            failwith
              ("Symmem.load_string failed to load a char"
             ^ "\nThe value loaded was: " ^ Expression.to_string sb)
      in
      if b = 0 then acc else loop (Int64.add a 1L) (acc ^ Char.(escaped (chr b)))
    in
    loop a ""

  let store_value (expr_to_value : Expression.t -> Num.t) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (value : Expression.t) :
    ((t * Expression.t list) list, bug) result =
    failwith "not implemented"

  let store_packed (expr_to_value : Expression.t -> Num.t) (sz : pack_size) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (value : Expression.t) :
    ((t * Expression.t list) list, bug) result =
    failwith "not implemented"

  let to_string (m : t) : string = MB.to_string m

  let to_heap (m : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t * (int32, int32) Hashtbl.t =
    (MB.to_heap m expr_to_value, Hashtbl.create 128) (* LEGACY HASHTBL RETURN, WAS OLD CHUNKTABLE*)

  (*TODO : change int32 to address (int64)*)
  let alloc (check_concr : Expression.t option -> bool) (expr_to_value : Expression.t -> Num.t)
    (m : t) (sym_b : Expression.t) (sym_s : Expression.t) : 
    (t * int32 * Expression.t list) list =
    failwith "not implemented"

  let check_bound (m : t) (b : int32) : bool = 
    failwith "not implemented"

  let free (m : t) (b : int32) : (unit, bug) result = 
    failwith "not implemented"

end