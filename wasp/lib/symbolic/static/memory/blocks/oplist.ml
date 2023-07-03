open Encoding
open Value
open Expression
open Types


module OpList : Block.M = struct
  type address = int32

  type op = Expression.t * Expression.t (* offset * value *)
  type t = (address, Expression.t * op list) Hashtbl.t (* address, block_size * operations *)

  exception Bounds

  let init () : t = Hashtbl.create Interpreter.Flags.hashtbl_default_size

  let to_string (h : t) : string =
    Hashtbl.fold
    (fun k (sz, ops) accum -> 
      accum 
      ^ Int32.to_string k
      ^ " -> ("
      ^ Expression.to_string sz
      ^ ", " ^ "["
      ^ String.concat ", "
          (List.map
             (fun (i, v) ->
               Expression.to_string i
               ^ " "
               ^ Expression.to_string v)
             ops)
      ^ "]" ^ ")")
    h ""


  let store_byte (h : t) (addr : address) (idx : Expression.t) (v : Expression.t) : unit =
    let arr' = Hashtbl.find_opt h addr in
    let f ((block_sz, oplist) : Expression.t * op list) : unit =
      Hashtbl.replace h addr (block_sz, (idx, v) :: oplist)
    in
    Option.fold ~none:() ~some:f arr'


  let store_n (h : t) (addr : address) (idx : Expression.t) (n : int) 
      (v : Expression.t) : unit =
    let rec loop mem a i n x =
      if n > i then (
        let x' = 
          match x with 
          | Extract (_, _, _) -> x 
          | _ -> Expression.Extract (x, i + 1, i) 
        in
        let idx' = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 (Int32.of_int i)))) in
        store_byte mem a idx' x';
        loop mem a (i + 1) n x)
    in
    loop h addr 0 n v


  let store (h : t) (addr : address) (idx : Expression.t) 
            (o : int32) (v : Expression.t)  (sz : int) :
            (t * Expression.t list) list =
    let idx' = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 o))) in
    store_n h addr idx' sz v;
    [ (h, []) ]


  let rec load_byte (check_sat_helper : Expression.t -> bool) (ops : op list) (idx : Expression.t) : 
    Expression.t =
    match ops with
    | [] -> Expression.Extract (Val (Num (I32 0l)), 1, 0)
    | (offset, v) :: op_list' ->
        let expr = Expression.Relop (I32 I32.Eq, idx, offset) in
        (* Printf.printf "\n%s\n" (Expression.to_string expr); *)
        if not (check_sat_helper expr) then
            v
        else load_byte check_sat_helper op_list' idx
    
  
  let load_n (check_sat_helper : Expression.t -> bool) (ops : op list) (idx : Expression.t) (n : int) :
      Expression.t list =
    let rec loop n acc =
      if n = 0 then acc
      else
        let idx' = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 (Int32.of_int (n-1))))) in
        let se = load_byte check_sat_helper ops idx' in
        loop (n - 1) (se :: acc)
    in
    loop n []


  let load (check_sat_helper : Expression.t -> bool) (h : t) 
    (addr : address) (idx : Expression.t) (o : int32) (sz : int) (ty : num_type) (is_packed : bool): 
    (t * Expression.t * Expression.t list) list =
    (* Printf.printf "\n\n%s\n\n" (to_string h); *)
    let arr' = Hashtbl.find h addr in
    let _, ops = arr' in
    let idx' = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 o))) in
    let exprs = load_n check_sat_helper ops idx' sz in
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
    (* Printf.printf "\n\n%s\n\n" (Expression.to_string expr); *)
    let expr = Expression.simplify expr in
    (* remove extract *)
    let v = Expression.simplify ~extract:true expr in
    (* Printf.printf "\n\n%s\n\n" (Expression.to_string expr);
    Printf.printf "\n\n%s\n\n" (Expression.to_string v); *)
    [ h, v, [] ]
      

  let from_heap (h : Concolic.Heap.t) : t =
    failwith "not implemented"


  let clone (h : t) : t * t = 
    let copy = Hashtbl.copy h in
    ( h, copy )


  let to_heap (h : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t =
    failwith "not implemented"


  let alloc (h : t) (b : address) (sz : Expression.t) : (t * int32 * Expression.t list) list =
    Hashtbl.replace h b (sz, []);
    [ ( h, b, [] ) ]


  let free (h : t) (addr : address) : unit =
    Hashtbl.remove h addr


  let check_bound (h : t) (addr : address) : bool =
    Hashtbl.mem h addr

  let is_within (block_sz : Expression.t) (index : Expression.t) (o : int32) (sz : int) : Expression.t = 
    let sz = Val (Num (I32 (Int32.of_int sz))) in
    let o = Val (Num (I32 o)) in
    let index = Expression.Binop (I32 I32.Add, index, o) in
    let e1 = Expression.Relop (I32 I32.LtS, index, Val (Num (I32 0l))) in
    let e2 = Expression.Relop (I32 I32.GtS, Expression.Binop (I32 I32.Add, index, sz), block_sz) in
    Expression.Binop (Bool B.Or, e1, e2)
    (*Expression.Relop (Bool B.Eq, Expression.Binop (Bool B.Or, e1, e2), Val (Bool true)) (* To work with batch *)*)



  let in_bounds (h : t) (addr : address) (idx : Expression.t) (o : int32) (sz : int) : Expression.t =
    (* Hashtbl.iter (fun x (y, z) -> Printf.printf "addr: %d  size: %s\n" (x) (Expression.to_string y)) h;
    Printf.printf "%s %s %s %d" (Int32.to_string addr) (Int32.to_string o) (Expression.to_string idx) (sz);  *)
    (match Hashtbl.find_opt h addr with
    | Some (block_sz, _)  -> 
        (match block_sz with
        | Val (Num (I64 block_sz')) -> is_within (Val (Num (I32 (Int64.to_int32 block_sz')))) idx o sz
        | Val (Num (I32 _))
        | SymPtr _ -> is_within block_sz idx o sz
        | _ -> failwith ("InternalError: OpList.in_bounds, size not an integer or SymPtr"))
    | _ -> failwith ("InternalError: OpList.in_bounds, accessed OpList is not in the heap"))

end