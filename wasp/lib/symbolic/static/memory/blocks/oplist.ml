open Encoding
open Value
open Expression
open Types


module OpList : Block.M = struct
  type address = int

  type op = Expression.t * Expression.t * int (* offset * value * size *)
  type t = (address, Expression.t * op list) Hashtbl.t (* address, block_size * operations *)

  exception Bounds

  let init () : t = Hashtbl.create Interpreter.Flags.hashtbl_default_size

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
             (fun (i, v, s) ->
               Expression.to_string i
               ^ " "
               ^ Expression.to_string v
               ^ " "
               ^ Int.to_string s)
             ops)
      ^ "]" ^ ")")
    h ""


  let store (h : t) (addr : int32) (idx : Expression.t) (o : int32) (v : Expression.t) (sz : int) =
    let arr' = Hashtbl.find_opt h (Int32.to_int addr) in 
    let offset = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 o))) in               
    let f ((block_sz, oplist) : Expression.t * op list) : unit =
      Hashtbl.replace h (Int32.to_int addr) (block_sz, (offset, v, sz) :: oplist)
    in
    Option.fold ~none:() ~some:f arr'


  let rec load_op (check_sat_helper : Expression.t -> bool) (op_list : op list) (idx : Expression.t) (size : int) : Expression.t =
    match op_list with
    | [] -> failwith "unaligned read"
    | (offset, v, size') :: op_list' ->
        let expr = Expression.Relop (I32 I32.Eq, idx, offset) in
        if (check_sat_helper expr) then
          if (size' >= size) then
            Expression.Extract (v, 0, size-1)
          else failwith "unaligned read"
        else load_op check_sat_helper op_list' idx size


  let load (check_sat_helper : Expression.t -> bool) (h : t) (addr : int32) (idx : Expression.t) (o : int32) (sz : int) : Expression.t =
    let arr' = Hashtbl.find h (Int32.to_int addr) in
    let _, ops = arr' in
    let idx' = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 o))) in (* currently in wasp addresses are I32, in the future change to I64*)

    (* let target_ops = load_op target_bytes (List.rev ops) in
    target_ops; *)
    let expr = load_op check_sat_helper ops idx' sz in
    Expression.simplify ~extract:true expr
      

  let from_heap (h : Concolic.Heap.t) : t =
    failwith "not implemented"


  let clone (h : t) : t * t = 
    let copy = Hashtbl.copy h in
    ( h, copy )


  let to_heap (h : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t =
    failwith "not implemented"


  let alloc (h : t) (b : int32) (sz : Expression.t) : unit =
    Hashtbl.replace h (Int32.to_int b) (sz, [])


  let free (h : t) (addr : int32) : unit =
    Hashtbl.remove h (Int32.to_int addr)


  let check_bound (h : t) (addr : int32) : bool =
    Hashtbl.mem h (Int32.to_int addr)

  let is_within (block_sz : Expression.t) (index : Expression.t) (sz : int) : Expression.t = 
    let sz = Val (Num (I64 (Int64.of_int sz))) in
    let e1 = Expression.Relop (I64 I64.LtS, index, Val (Num (I64 0L))) in
    let e2 = Expression.Relop (I64 I64.GeS, Expression.Binop (I64 I64.Add, index, sz), block_sz) in
    Expression.Binop (I64 I64.Or, e1, e2)


  let in_bounds (h : t) (addr : int32) (idx : Expression.t) (sz : int) : Expression.t =
    (match Hashtbl.find_opt h (Int32.to_int addr) with 
    | Some (block_sz, _)  -> 
        (match block_sz with
        | Val (Num (I64 _))
        | SymPtr _ -> is_within block_sz idx sz
        | _ -> failwith ("InternalError: HeapOpList.in_bounds, size not an integer or SymPtr"))
    | _ -> failwith ("InternalError: HeapOpList.in_bounds, accessed OpList is not in the heap"))

end