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

  let effective_address (a : address) (o : offset) : address =
    let ea = Int64.(add a (of_int32 o)) in
    if Interpreter.I64.lt_u ea a then raise MB.Bounds;
    ea

  
  let expr_to_value (ex : expr) (encoder : E.t) (v : Varmap.t) : Encoding.Num.t =
    let store_r = ref None in
    let store =
      match !store_r with
      | Some store -> store
      | None ->
          assert (E.check encoder None);
          let binds =
            E.value_binds encoder ~symbols:(Varmap.binds v)
          in
          let store = Concolic.Store.create binds in
          store_r := Some store;
          store
    in
    Concolic.Store.eval store ex

  let concr_ptr (sym_ptr : Expression.t ) (encoder : E.t) (v : Varmap.t) = 
    let sym_ptr = simplify sym_ptr in
    let ptr =
      match concretize_ptr sym_ptr with
      | Some ptr -> ptr
      | None -> expr_to_value sym_ptr encoder v
    in
    let open Interpreter in
    (I64_convert.extend_i32_u
      (Values.I32Value.of_value (Evaluations.to_value ptr)), ptr)


  let length_pack_size (sz : pack_size) : int =
    match sz with Pack8 -> 1 | Pack16 -> 2 | Pack32 -> 4

  (*let storen (mem : MB.t) (a : address) (o : offset) (n : int)
      (value : Expression.t) : unit =
    let rec loop mem a i n x =
      if n > i then (
        MB.store_byte mem a (Expression.Extract (x, i + 1, i));
        loop mem (Int64.add a 1L) (i + 1) n x)
    in
    loop mem (effective_address a o) 0 n value *)

  let loadn (mem : t) (a : address) (n : int) :
    Expression.t list =
    let rec loop a n acc =
      if n = 1 then acc
      else
        let se = Hashtbl.find mem.fixed a in
        loop (Int64.sub a 1L) (n - 1) (se :: acc)
    in
    loop Int64.(add a (of_int (n - 1))) n []


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
    match sym_ptr with
    | SymPtr (ptr_b, ptr_o) -> (* Load from memory *)
        let sz = Types.size_of_num_type ty in
        (* Printf.printf "LOAD: idx: %s + %s " (Int32.to_string ptr_b) (Int32.to_string o); *)
        let bounds_exp = MB.in_bounds mem.blocks ptr_b ptr_o o sz in
        if (check_sat encoder bounds_exp) then
          let check_sat_helper (expr : Expression.t) : bool =
            check_sat encoder expr
          in
          let res = MB.load check_sat_helper mem.blocks ptr_b ptr_o o sz ty false in
          let res' = List.map (fun (mb, v, c) -> 
            (* Printf.printf "v: %s\n"  (Expression.to_string v); *)
            (let fixed' = Hashtbl.copy mem.fixed in
            ( {blocks = mb; fixed = fixed'}, v, c))) res in (* SHOULD CLEAN UNSAT CONDS *)
          Result.ok (res')
        else Result.error (OOB)
    | _ -> (* Load from fixed *)
      let a, _ = concr_ptr sym_ptr encoder varmap in
      let ea = effective_address a o in
      (* Printf.printf "LOAD: idx: %s + %s " (Int64.to_string a) (Int32.to_string o); *)
      (* Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" (Int64.to_string x) (Expression.to_string y)) mem.fixed; *)
      let v = Hashtbl.find_opt mem.fixed ea in
      let v = match v with
      | Some v ->
          (match v with
          | Extract (e, h, l) -> (
            let sz = Types.size_of_num_type ty in 
            let exprs = v :: loadn mem ea sz in
            let expr =
              List.(
                fold_left
                  (fun acc e -> Expression.Concat (e, acc))
                  (hd exprs) (tl exprs))
            in
            (* simplify concats *)
            let expr = Expression.simplify expr in
            (* remove extract *)
            let expr = Expression.simplify ~extract:true expr in
            match ty with
            | `I32Type -> (
                match expr with
                | Val (Num (I64 v)) -> Val (Num (I32 (Int64.to_int32 v)))
                | _ -> expr)
            | `I64Type -> expr
            | `F32Type -> (
                match expr with
                | Val (Num (I64 v)) -> Val (Num (F32 (Int64.to_int32 v)))
                | Cvtop (I32 I32.ReinterpretFloat, v) -> v
                | _ -> Cvtop (F32 F32.ReinterpretInt, expr))
            | `F64Type -> (
                match expr with
                | Val (Num (I64 v)) -> Val (Num (F64 v))
                | Cvtop (I64 I64.ReinterpretFloat, v) -> v
                | _ -> Cvtop (F64 F64.ReinterpretInt, expr)))
          | _ -> v)
      | None -> Val (Num (I32 0l))
      in
      (* Printf.printf "v: %s\n"  (Expression.to_string v); *)
      let ptr_cond = [] in
      let res = [ (mem, v, ptr_cond) ] in
      Result.ok (res)


  let load_packed (encoder : E.t) (varmap : Varmap.t) (sz : pack_size) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (ty : num_type) :
    ((t * Expression.t * Expression.t list) list, bug) result =
    match sym_ptr with
    | SymPtr (ptr_b, ptr_o) -> (* Load from memory *)
        let sz = length_pack_size sz in
        (* Printf.printf "LOAD PACK %d: idx: %s + %s " (sz) (Int32.to_string ptr_b) (Int32.to_string o); *)
        let bounds_exp = MB.in_bounds mem.blocks ptr_b ptr_o o sz in
        if (check_sat encoder bounds_exp) then
          let check_sat_helper (expr : Expression.t) : bool =
            check_sat encoder expr
          in
          let res = MB.load check_sat_helper mem.blocks ptr_b ptr_o o sz ty true in
          let res' = List.map (fun (mb, v, c) -> 
            (* Printf.printf "v: %s\n"  (Expression.to_string v); *)
            (let fixed' = Hashtbl.copy mem.fixed in
            ( {blocks = mb; fixed = fixed'}, v, c))) res in (* SHOULD CLEAN UNSAT CONDS *)
          Result.ok (res')
         
        else Result.error (OOB)
    | _ -> (* Load from fixed *)
      let a, _ = concr_ptr sym_ptr encoder varmap in
      let ea = effective_address a o in
      
      (* Printf.printf "LOAD PACK %d: idx: %s + %s " (length_pack_size sz) (Int64.to_string a) (Int32.to_string o); *)
      (* Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" (Int64.to_string x) (Expression.to_string y)) mem.fixed; *)

      let v = Hashtbl.find_opt mem.fixed ea in
      let v = match v with
      | Some v ->
        (match v with 
          | Extract (e, h, l) -> (
              let sz = length_pack_size sz in
              let exprs = v :: loadn mem ea sz in
              let expr =
                List.(
                  fold_left
                    (fun acc e -> Expression.Concat (e, acc))
                    (hd exprs) (tl exprs))
              in
              (* simplify concats *)
              let expr = Expression.simplify expr in
              (* remove extract *)
              let expr = Expression.simplify ~extract:true expr in
              match ty with
              | `I32Type -> (
                  match expr with
                  | Val (Num (I64 v)) -> Val (Num (I32 (Int64.to_int32 v)))
                  | _ -> expr)
              | `I64Type -> expr
              | `F32Type -> (
                  match expr with
                  | Val (Num (I64 v)) -> Val (Num (F32 (Int64.to_int32 v)))
                  | Cvtop (I32 I32.ReinterpretFloat, v) -> v
                  | _ -> Cvtop (F32 F32.ReinterpretInt, expr))
              | `F64Type -> (
                  match expr with
                  | Val (Num (I64 v)) -> Val (Num (F64 v))
                  | Cvtop (I64 I64.ReinterpretFloat, v) -> v
                  | _ -> Cvtop (F64 F64.ReinterpretInt, expr)))
          | _ -> v)
      | None -> Val (Num (I32 0l))
      in
      (* Printf.printf "v: %s\n"  (Expression.to_string v); *)
      let ptr_cond = [] in
      let res = [ (mem, v, ptr_cond) ] in
      Result.ok (res)

  let load_string (mem : t) (a : address) : string =
    let rec loop a acc =
      let sb = Hashtbl.find mem.fixed a in
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

  let store_value (encoder : E.t) (varmap : Varmap.t) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (value : Expression.t) :
    ((t * Expression.t list) list, bug) result = 
    match sym_ptr with
    | SymPtr (ptr_b, ptr_o) -> (* Store to memory *)
        let ty = Expression.type_of value in
        let sz = Types.size ty in
        (* Printf.printf "STORE: %s + %s -> %s\n" (Int32.to_string ptr_b) (Int32.to_string o) (Expression.to_string value); *)
        let bounds_exp = MB.in_bounds mem.blocks ptr_b ptr_o o sz in
        (* Printf.printf " %s\n %s " (Expression.to_string bounds_exp) (Expression.to_string (E.get_assertions encoder)); *)
        if (check_sat encoder bounds_exp) then
          (let res = MB.store mem.blocks ptr_b ptr_o o value sz in
          let res' = List.map (fun (mb, c) -> 
            (let fixed' = Hashtbl.copy mem.fixed in
            ( {blocks = mb; fixed = fixed'}, c))) res in (* SHOULD CLEAN UNSAT CONDS *)
          Result.ok (res'))
        else Result.error (Overflow)
    | _ -> (* Store to fixed *)
      let a, _ = concr_ptr sym_ptr encoder varmap in
      let ea = effective_address a o in
      (* Printf.printf "STORE: %s + %s -> %s\n" (Int64.to_string a) (Int32.to_string o) (Expression.to_string value); *)
      Hashtbl.replace mem.fixed ea value;
      let ptr_cond = [] in
      let res = [ (mem, ptr_cond) ] in
      Result.ok (res)


  let store_packed (encoder : E.t) (varmap : Varmap.t) (sz : pack_size) (mem : t) 
    (sym_ptr : Expression.t) (o : offset) (value : Expression.t) :
    ((t * Expression.t list) list, bug) result =
    match sym_ptr with
    | SymPtr (ptr_b, ptr_o) -> (* Store to memory *)
        let sz = length_pack_size sz in
        (* Printf.printf "STORE PACKED: %s + %s -> %s\n" (Int32.to_string ptr_b) (Int32.to_string o) (Expression.to_string value); *)
        let bounds_exp = MB.in_bounds mem.blocks ptr_b ptr_o o sz in
        (* Printf.printf " %s\n %s " (Expression.to_string bounds_exp) (Expression.to_string (E.get_assertions encoder)); *)
        if (check_sat encoder bounds_exp) then
          (let res = MB.store mem.blocks ptr_b ptr_o o value sz in
          let res' = List.map (fun (mb, c) -> 
            (let fixed' = Hashtbl.copy mem.fixed in
            ( {blocks = mb; fixed = fixed'}, c))) res in (* CLEAN UNSAT CONDS *)
          Result.ok (res'))
        else Result.error (Overflow)
    | _ -> (* Store to fixed *)
      let a, _ = concr_ptr sym_ptr encoder varmap in
      let ea = effective_address a o in
      (* Printf.printf "STORE PACKED: %s + %s -> %s\n" (Int64.to_string a) (Int32.to_string o) (Expression.to_string value); *)
      Hashtbl.replace mem.fixed ea value;
      let ptr_cond = [] in
      let res = [ (mem, ptr_cond) ] in
      Result.ok (res)

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
        let res = MB.alloc m.blocks base sym_s in
        if List.length res = 1 then
          [ (m, base, [])]
        else
        List.map (fun (mb, a, c) -> 
          (let fixed' = Hashtbl.copy m.fixed in
          ( {blocks = mb; fixed = fixed'}, a, c))) res
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

module ArrayConcrSMem = SMem (Arrayconcr.ArrayConcr)
module ArrayForkSMem = SMem (Arrayfork.ArrayFork)
module ArrayITESMem = SMem (Arrayite.ArrayITE)
module OpListSMem = SMem (Oplist.OpList)