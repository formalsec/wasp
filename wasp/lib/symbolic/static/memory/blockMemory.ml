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


module SMem (MB : Block.M) (E : Common.Encoder) : SymbolicMemory with type e = E.t = struct
  type t = {blocks: MB.t; fixed: (address, Expression.t) Hashtbl.t}
  type e = E.t
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

  let check_sat (e : E.t) (expr : Expression.t) : bool =
    not (E.check e (Some expr))

  (* Public functions *)
  let from_heap (map : Concolic.Heap.t) : t =
    let concolic_seq = Concolic.Heap.to_seq map in
    let concolic_to_symbolic (k, (_, s)) = (k, s) in
    let fixed = Hashtbl.of_seq (Seq.map concolic_to_symbolic concolic_seq) in
    { blocks = MB.init (); fixed }

  let clone (m : t) : t * t =
    let blocks1, blocks2 = MB.clone m.blocks in
    let fixed1 = m.fixed in
    let fixed2 = Hashtbl.copy m.fixed in
    ( { blocks = blocks1; fixed = fixed1 },
      { blocks = blocks2; fixed = fixed2 } )

  let check_access (m : t) (sym_ptr : Expression.t) (ptr : Num.t) (o : offset) : bug option =
    let base_ptr = concretize_base_ptr sym_ptr in
    ignore base_ptr;
    failwith "not implemented"

  let load_value (encoder : E.t) (varmap : Varmap.t) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (ty : num_type) :
    ((t * Expression.t * Expression.t list) list, bug) result =
    let ptr_b, ptr_o =
      match sym_ptr with
      | SymPtr (base, offset) -> base, offset
      | _ -> failwith "Unreachable"
    in
    let sz = Types.size_of_num_type ty in
    let bounds_exp = MB.in_bounds mem.blocks ptr_b ptr_o sz in
    if (check_sat encoder bounds_exp) then
      let check_sat_helper (expr : Expression.t) : bool =
        check_sat encoder expr
      in
      let v = MB.load check_sat_helper mem.blocks ptr_b ptr_o o sz in
      let ptr_cond = [] in
      let res = [ (mem, v, ptr_cond) ]
      in
      Result.ok (res)
    else Result.error (OOB)


  let load_packed (encoder : E.t) (varmap : Varmap.t) (sz : pack_size) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (ty : num_type) :
    ((t * Expression.t * Expression.t list) list, bug) result =
    failwith "not implemented"

  let load_string (mem : t) (a : address) : string =
    failwith "not implemented"

  let store_value (encoder : E.t) (varmap : Varmap.t) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (value : Expression.t) :
    ((t * Expression.t list) list, bug) result =
    let ptr_b, ptr_o =
      match sym_ptr with
      | SymPtr (base, offset) -> base, offset
      | _ -> failwith "Unreachable"
    in
    let ty = Expression.type_of value in
    let sz = Types.size ty in
    let bounds_exp = MB.in_bounds mem.blocks ptr_b ptr_o sz in
    if not (E.check encoder (Some bounds_exp)) then
      (* let pc = E.get_assertions encoder in *)
      (MB.store mem.blocks ptr_b ptr_o o value sz; (* Should send path condition for merging *)
      let ptr_cond = [] in
      let res = [ (mem, ptr_cond) ]
      in
      Result.ok (res))
    else Result.error (Overflow)

  let store_packed (encoder : E.t) (varmap : Varmap.t) (sz : pack_size) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (value : Expression.t) :
    ((t * Expression.t list) list, bug) result =
    failwith "not implemented"

  let to_string (m : t) : string = MB.to_string m.blocks

  let to_heap (m : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t * (int32, int32) Hashtbl.t =
    (MB.to_heap m.blocks expr_to_value, Hashtbl.create 128) (* LEGACY HASHTBL RETURN, WAS OLD CHUNKTABLE*)

  (*TODO : change int32 to address (int64)*)
  let alloc (encoder : E.t) (varmap : Varmap.t)
    (m : t) (sym_b : Expression.t) (sym_s : Expression.t) : 
    (t * int32 * Expression.t list) list =
    match (sym_s, sym_b) with
    |  _, Val (Num (I32 base)) -> 
        MB.alloc m.blocks base sym_s;
        (m, base, []) :: []
    | _, _ ->  failwith "Unreachable"


  let check_bound (m : t) (b : int32) : bool = MB.check_bound m.blocks b

  let free (m : t) (b : int32) : (unit, bug) result = 
    if not (check_bound m b) then (
      Result.error(InvalidFree)
    )
    else (
      Result.ok (MB.free m.blocks b)
    )

end

module OpListSMem = SMem (Oplist.OpList)