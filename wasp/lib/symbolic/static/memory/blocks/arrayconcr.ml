open Encoding
open Value
open Expression
open Types
open Operators

module ArrayConcr : Block.M = struct
  type address = int32
  type expr = Expression.t
  type  bt = Expression.t array
  type   t = (address, bt) Hashtbl.t

  exception Bounds

  let init () : t = Hashtbl.create Interpreter.Flags.hashtbl_default_size

  let block_str (block : bt) : string =
    let blockList = Array.to_list block in
    String.concat ", " (List.map (fun el -> Expression.to_string el) blockList)


  let to_string (heap: t) : string =
    Hashtbl.fold (fun _ b acc -> (block_str b) ^ "\n" ^ acc) heap ""

  
  let store_byte (h : t) (addr : address) (idx : int) (v : Expression.t) : unit =
    let block = Hashtbl.find h addr in
    Array.set block idx v;
    Hashtbl.replace h addr block


  let store_n (h : t) (addr : address) (o : int) (idx : int) (n : int) 
    (v : Expression.t) : unit =
    let rec loop mem a i n x =
      if n > i then (
        let x' = 
          match x with 
          | Extract (_, _, _) -> x 
          | _ -> Expression.Extract (x, i + 1, i) 
        in
        store_byte mem a (idx+o+i) x';
        loop mem a (i + 1) n x)
    in
    loop h addr 0 n v
  

  let store (expr_to_value : (expr -> expr -> Num.t)) (check_sat_helper : Expression.t -> bool)
    (h : t) (addr : address) (idx : Expression.t) 
    (o : int32) (v : Expression.t)  (sz : int) :
    (t * Expression.t list) list =
    let idx = Expression.simplify idx in
    let idx', conds = 
      match idx with
      (* Store in concrete index *)
      | Val (Num (I32 idx')) -> idx', []
      (* Store in symbolic index, randomly concretizes *)
      | _ ->
        let block = Hashtbl.find h addr in
        let block_sz = Array.length block in
        let o' = Val (Num (I32 o)) in
        let index = Expression.Binop (I32 I32.Add, idx, o') in
        let c = 
          Relop (I32 I32.LtS, index, Val (Num (I32 (Int32.of_int block_sz)))) in
        (* Get from path condition, if not there concretize and add to it *)
        let idx' = 
          match (expr_to_value idx c) with
          | I32 n -> n
          | I64 n -> Int64.to_int32 n
          | _     -> assert false
        in
        let cond = 
          Relop (I32 I32.Eq, idx, Val (Num (I32 (idx')))) in
        ( idx', [ cond ] )
    in
    store_n h addr (Int32.to_int o) (Int32.to_int idx') sz v;
    [ ( h, conds ) ]


  let load_byte (h : t) (addr : address) (idx : int) : 
    Expression.t =
    let block = Hashtbl.find h addr in
    Array.get block idx
    
  
  let load_n (mem : t) (a : address) (o : int) (idx : int) (n : int) :
      Expression.t list =
    let rec loop a n acc =
      if n = 0 then acc
      else
        let se = load_byte mem a (idx+o+n-1) in
        loop a (n - 1) (se :: acc)
    in
    loop a n []


  let load (expr_to_value : (expr -> expr -> Num.t)) (check_sat_helper : Expression.t -> bool) 
    (h : t) (addr : address) (idx : Expression.t) (o : int32) (sz : int) (ty : num_type) 
    (is_packed : bool) : 
    (t * Expression.t * Expression.t list) list =
    ignore check_sat_helper;
    let idx = Expression.simplify idx in
    let idx', conds = 
      match idx with
      (* Load in concrete index *)
      | Val (Num (I32 idx')) -> idx', []
      (* Load in symbolic index, randomly concretizes *)
      | _ ->
        let block = Hashtbl.find h addr in
        let block_sz = Array.length block in
        let o' = Val (Num (I32 o)) in
        let index = Expression.Binop (I32 I32.Add, idx, o') in
        let index = Expression.simplify index in
        let c = 
          Relop (I32 I32.LtS, index, Val (Num (I32 (Int32.of_int block_sz)))) in
        (* Get from path condition, if not there concretize and add to it *)
        let idx' = 
          match (expr_to_value idx c) with
          | I32 n -> n
          | I64 n -> Int64.to_int32 n
          | _     -> assert false
        in
        let cond = 
          Relop (I32 I32.Eq, idx, Val (Num (I32 (idx')))) in
        ( idx', [ cond ] )
    in
    let exprs = load_n h addr (Int32.to_int o) (Int32.to_int idx') sz in
    let v = concat_exprs exprs ty sz is_packed in
    [ ( h, v, conds ) ]
      

  let from_heap (h : Concolic.Heap.t) : t =
    failwith "not implemented"


  let clone (h : t) : t * t = 
    let copy = Hashtbl.copy h in
    Hashtbl.iter (fun x y -> Hashtbl.replace copy x (Array.copy y)) h; 
    ( h, copy )


  let to_heap (h : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t =
    failwith "not implemented"


  let alloc (check_sat_helper : Expression.t option -> bool) (h : t) 
    (b : address) (sz : Expression.t) (binds : (Symbol.t * Value.t) list): 
    (t * int32 * Expression.t list) list =    match sz with
    (* concrete alloc *)
    |  Val (Num (I32 sz)) ->        (* Should init this with None instead *)
      Hashtbl.replace h b (Array.make (Int32.to_int sz) (Extract (Val (Num (I32 0l)), 1, 0)));
      [ (h, b, []) ]
    (* sym alloc *)
    | _ ->  
      let helper (c_size : int32 option) : 
      (t * int32 * Expression.t list) option =
      let size_cond =
        Option.map
          (function c_size -> Relop (I32 I32.Eq, sz, Val (Num (I32 c_size))))
          c_size
      in
      match check_sat_helper size_cond with
      | false -> None
      | true ->
          let logic_env = Concolic.Store.create binds in
          let c_size = Concolic.Store.eval logic_env sz in
          let c, mc = clone h in
          let size = 
            match c_size with
            | I32 size -> size
            | _ -> failwith "Alloc non I32 size"
          in
          (match size_cond with
            | Some size_cond -> 
                Hashtbl.replace mc b (Array.make (Int32.to_int size) (Extract (Val (Num (I32 0l)), 1, 0)));
                Some (mc, b, [ size_cond ])
            | None -> 
                Hashtbl.replace c b (Array.make (Int32.to_int size) (Extract (Val (Num (I32 0l)), 1, 0)));
                Some (c, b, [])) (* MAYBE BUG WITH MEM CLONING?? *)

      in
      let fixed_attempts =
        List.filter_map helper
          (List.map Option.some
              (List.map Int32.of_int !Interpreter.Flags.fixed_numbers))
      in
      if List.length fixed_attempts > 0 then fixed_attempts
      else [ Option.get (helper None) ]



  let free (h : t) (addr : address) : unit =
    Hashtbl.remove h addr


  let check_bound (h : t) (addr : int32) : bool =
    Hashtbl.mem h addr

  let is_within (block_sz : int) (index : Expression.t) (o : int32) (sz : int) : Expression.t = 
    let block_sz = Val (Num (I32 (Int32.of_int block_sz))) in
    let sz = Val (Num (I32 (Int32.of_int sz))) in
    let o = Val (Num (I32 o)) in
    let index = Expression.Binop (I32 I32.Add, index, o) in
    let e1 = Expression.Relop (I32 I32.LtS, index, Val (Num (I32 0l))) in
    let e2 = Expression.Relop (I32 I32.GtS, Expression.Binop (I32 I32.Add, index, sz), block_sz) in
    Expression.Binop (Bool B.Or, e1, e2)
    (*Expression.Relop (Bool B.Eq, Expression.Binop (Bool B.Or, e1, e2), Val (Bool true)) (* To work with batch *)*)



  let in_bounds (h : t) (addr : address) (idx : Expression.t) (o : int32) (sz : int) : Expression.t =
    (match Hashtbl.find_opt h addr with
      | Some a -> is_within (Array.length a) idx o sz
      | _ -> failwith ("InternalError: ArrayConcr.in_bounds, accessed array is not in the heap"))
end