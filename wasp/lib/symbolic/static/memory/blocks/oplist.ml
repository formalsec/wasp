open Encoding
open Value
open Expression
open Types


module OpList : Block.M = struct
  type address = int

  type op = Expression.t * Expression.t * Expression.t list (* path condition *)
  type t = (address, Expression.t * op list) Hashtbl.t

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
             (fun (i, v, _) ->
               Expression.to_string i
               ^ " "
               ^ Expression.to_string v)
             ops)
      ^ "]" ^ ")")
    h ""


  let store (h : t) (addr : int32) (idx : Expression.t) (o : int32) (v : Expression.t) (pc : Expression.t list) =
    let arr' = Hashtbl.find_opt h (Int32.to_int addr) in 
    let offset = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 o))) in               
    let f ((sz, oplist) : Expression.t * op list) : unit =
      Hashtbl.replace h (Int32.to_int addr) (sz, (offset, v, pc) :: oplist)
    in
    Option.fold ~none:() ~some:f arr'


  let load (h : t) (addr : int32) (idx : Expression.t) (o : int32) (ty : num_type) : Expression.t =
    let arr' = Hashtbl.find h (Int32.to_int addr) in
    let _, ops = arr' in
    let (op : relop), def =
      match ty with
      | `I32Type -> I32 I32.Eq, Val (Num (I32 0l))
      | `I64Type -> I64 I64.Eq, Val (Num (I64 0L))
      | `F32Type -> F32 F32.Eq, Val (Num (F32 0l))
      | `F64Type -> F64 F64.Eq, Val (Num (F64 0L))
    in
    let offset = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 o))) in 
    List.fold_left
      (fun ac (i, v, _) -> 
        Expression.Triop (Bool B.ITE, Expression.Relop (op, offset, i), v, ac))
      def (List.rev ops)


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

  let is_within (sz : Expression.t) (index : Expression.t) : Expression.t = 
    let e1 = Expression.Relop (I64 I64.LtS, index, Val (Num (I64 0L))) in
    let e2 = Expression.Relop (I64 I64.GeS, index, sz) in
    Expression.Binop (I64 I64.Or, e1, e2)


  let in_bounds (h : t) (addr : int32) (idx : Expression.t) : Expression.t =
    (match Hashtbl.find_opt h (Int32.to_int addr) with 
    | Some (sz, _)  -> 
        (match sz with
        | Val (Num (I64 _))
        | SymPtr _ -> is_within sz idx
        | _ -> failwith ("InternalError: HeapOpList.in_bounds, size not an integer or SymPtr"))
    | _ -> failwith ("InternalError: HeapOpList.in_bounds, accessed OpList is not in the heap"))

end