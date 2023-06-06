open Encoding
open Value
open Expression
open Types


module OpList (E : Common.Encoder) : Block.M = struct
  type address = int

  type op = Expression.t * Expression.t * Expression.t list (* path condition *)
  type t = { map : (address, Expression.t * op list) Hashtbl.t; mutable next : int }
  type e = E.t

  let init () : t = { map = Hashtbl.create Interpreter.Flags.hashtbl_default_size; next = 0 }

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


  let store (h : t) (addr : Expression.t) (idx : Expression.t) (v : Expression.t) (pc : Expression.t list) =
    let lbl = 
      match addr with 
      | Val (Int i) -> i 
      | _ -> failwith "OpList: Block address not an integer"
    in
    let arr' = Hashtbl.find_opt h.map lbl in                
    let f ((sz, oplist) : Expression.t * op list) : unit =
      Hashtbl.replace h.map lbl (sz, (idx, v, pc) :: oplist)
    in
    Option.fold ~none:() ~some:f arr'


  let load (h : t) (addr : Expression.t) (idx : Expression.t) (ty : num_type) : Expression.t =
    let lbl = 
      match addr with 
      | Val (Int i) -> i 
      | _ -> failwith "OpList: Block address not an integer"
    in
    let arr' = Hashtbl.find h.map lbl in
    let _, ops = arr' in
    let (op : relop), def =
      match ty with
      | `I32Type -> I32 I32.Eq, Val (Num (I32 0l))
      | `I64Type -> I64 I64.Eq, Val (Num (I64 0L))
      | `F32Type -> F32 F32.Eq, Val (Num (F32 0l))
      | `F64Type -> F64 F64.Eq, Val (Num (F64 0L))
    in
    List.fold_left
      (fun ac (i, v, _) -> (* build ITE auxiliary function *)
        Expression.Triop (Bool B.ITE, Expression.Relop (op, idx, i), v, ac))
      def (List.rev ops)


  let from_heap (h : Concolic.Heap.t) : t =
    failwith "not implemented"


  let clone (h : t) : t * t = 
    let copy = Hashtbl.copy h.map in
    ( h, { map = copy; next = h.next } )


  let to_heap (h : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t =
    failwith "not implemented"


  let alloc (h : t) (sz : Expression.t) : unit =
    let next = h.next in
    Hashtbl.add h.map next (sz, []);
    h.next <- h.next + 1


  let free (h : t) (addr : Expression.t) : unit =
    let lbl = 
        match addr with 
        | Val (Int i) -> i 
        | _ -> failwith "OpList: Block address not an integer"
    in
    Hashtbl.remove h.map lbl


  let is_within (sz : Expression.t) (index : Expression.t) (encoder : E.t) : bool = 
    let e1 = Expression.Relop (I64 I64.LtS, index, Val (Num (I64 0L))) in
    let e2 = Expression.Relop (I64 I64.GeS, index, sz) in
    let e3 = Expression.Binop (I64 I64.Or, e1, e2) in

    not (E.check encoder (Some e3))


  let in_bounds (h : t) (addr : Expression.t) (idx : Expression.t) (encoder : E.t) : bool =
    match addr with  
    | Val Int l -> 
      (match Hashtbl.find_opt h.map l with 
      | Some (sz, _)  -> 
          (match sz with
          | Val (Num (I64 _))
          | SymPtr _ -> is_within sz idx encoder
          | _ -> failwith ("InternalError: HeapOpList.in_bounds, size not an integer or SymPtr"))
      | _ -> failwith ("InternalError: HeapOpList.in_bounds, accessed OpList is not in the heap"))
    | _ -> failwith ("InternalError: HeapOpList.in_bounds, addr must be an integer")

end