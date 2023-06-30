open Encoding
open Value
open Expression
open Types


module ArrayITE : Block.M = struct
  type address = int32

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
    

  let store (h : t) (addr : address) (idx : Expression.t) 
            (o : int32) (v : Expression.t)  (sz : int) : 
            (t * Expression.t list) list =
    let block = Hashtbl.find h addr in
    match idx with
    (* Store in concrete index *)
    | Val (Num (I32 idx')) -> 
      store_n h addr (Int32.to_int o) (Int32.to_int idx') sz v;
      [ ( h, [] ) ]
    (* Store in symbolic index *)
    | _ -> ignore block; failwith "not impl"
      (* let block' = Array.mapi (fun j old_expr -> 
        let e = BinOp(Equals,index,Val (Integer j)) in 
        if Translator.is_sat ([e] @ path) then Expression.ITE(e, v, old_expr)
        else old_expr) block in
      let _ = Hashtbl.replace heap' loc block' in
      [((heap', curr), path)] *)
      (* List.filteri (fun index' _ ->   (* can be optimized *)
        let e = BinOp(Equals,index,Val (Integer index')) in 
        if Translator.is_sat ([e] @ path) then true else false) temp *)


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
    
    
  let load (check_sat_helper : Expression.t -> bool) (h : t) (addr : address) 
    (idx : Expression.t) (o : int32) (sz : int) (ty : num_type) (is_packed : bool) : 
    (t * Expression.t * Expression.t list) list =
    ignore check_sat_helper;
    (* Printf.printf "\n\n%s\n\n" (to_string h); *)
    let idx', conds = 
      match idx with
      (* Load in concrete index *)
      | Val (Num (I32 idx')) -> idx', []
      (* Load in symbolic index, randomly concretizes *)
      | _ ->
        let block = Hashtbl.find h addr in
        let block_sz = Array.length block in
        let idx' = Int32.of_int (Random.int block_sz) in
        let cond = 
          Relop (I32 I32.Eq, idx, Val (Num (I32 (idx')))) in
        ( idx', [ cond ] )
    in
    let exprs = load_n h addr (Int32.to_int o) (Int32.to_int idx') sz in
    (* pad with 0s *)
    let expr = 
      if (not is_packed) then
        List.(
          fold_left
            (fun acc e -> Expression.Concat (e, acc))
            (hd exprs) (tl exprs))
      else
        let rec loop acc i =
          if i >= Types.size_of_num_type ty then acc
          else loop (acc @ [ Extract (Val (Num (I32 0l)), 1, 0) ]) (i + 1)
        in
        let exprs = loop exprs (List.length exprs) in
        List.(fold_left (fun acc e -> e ++ acc) (hd exprs) (tl exprs))
    in
    (* simplify concats *)
    let expr = Expression.simplify expr in
    (* remove extract *)
    let v = Expression.simplify ~extract:true expr in
    (* Printf.printf "\n\n%s\n\n" (Types.string_of_type (Expression.type_of expr));
    Printf.printf "\n\n%s\n\n" (Expression.to_string expr);
    Printf.printf "\n\n%s\n\n" (Expression.to_string v); *)
    [ ( h, v, [] ) ]


  let from_heap (h : Concolic.Heap.t) : t =
    failwith "not implemented"


  let clone (h : t) : t * t = 
    let copy = Hashtbl.copy h in
    Hashtbl.iter (fun x y -> Hashtbl.replace copy x (Array.copy y)) h; 
    ( h, copy )


  let to_heap (h : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t =
    failwith "not implemented"


  let alloc (h : t) (b : address) (sz : Expression.t) : (t * int32 * Expression.t list) list =
    match sz with
    (* concrete alloc *)
    |  Val (Num (I32 sz)) -> 
      Hashtbl.replace h b (Array.make (Int32.to_int sz) (Extract (Val (Num (I64 0L)), 1, 0)));
      [ (h, b, []) ]
    (* sym alloc *)
    | _ ->  
      [ (h, b, []) ] (* SYM ALLOCS *)



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
      | _ -> failwith ("InternalError: ArrayFork.in_bounds, accessed array is not in the heap"))
end