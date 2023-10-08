open Encoding
open Value
open Expression
open Types
open Operators

module OpList : Block.M = struct
  type address = int32
  type expr = Expression.t

  type cache = (address * Expression.t, int * Expression.t) Hashtbl.t (* address * offset, size * value *)
  type op = Expression.t * Expression.t (* offset * value *)
  type t = { mem : (address, Expression.t * op list) Hashtbl.t;
            cache : cache } (* address, block_size * operations *)

  exception Bounds

  let init () : t = { mem = Hashtbl.create Interpreter.Flags.hashtbl_default_size;
                    cache = Hashtbl.create Interpreter.Flags.hashtbl_default_size }

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
               ^ Expression.to_string v
               ^ "\n")
             ops)
      ^ "]" ^ ")")
    h.mem ""


  let store_byte (h : t) (addr : address) (idx : Expression.t) (v : Expression.t) : unit =
    let arr' = Hashtbl.find_opt h.mem addr in
    let f ((block_sz, oplist) : Expression.t * op list) : unit =
      let idx = Expression.simplify idx in
      Hashtbl.replace h.mem addr (block_sz, (idx, v) :: oplist)
    in
    Option.fold ~none:() ~some:f arr'


  let store_n (h : t) (addr : address) (idx : Expression.t) (n : int) 
      (v : Expression.t) : unit =
    let rec loop mem a i n x =
      if n > i then (
        let x' = 
          match x with 
          | Extract _ -> x 
          | _ -> Expression.Extract (x, i + 1, i) 
        in
        let idx' = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 (Int32.of_int i)))) in
        store_byte mem a idx' x';
        loop mem a (i + 1) n x)
    in
    loop h addr 0 n v


  let store (expr_to_value : (expr -> expr -> Num.t)) (check_sat_helper : Expression.t -> bool)
    (h : t) (addr : address) (idx : Expression.t) 
    (o : int32) (v : Expression.t)  (sz : int) :
    (t * Expression.t list) list =
    let idx' = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 o))) in
    let idx' = Expression.simplify idx' in
    (match idx' with
    (* Store in concrete index *)
    | Val (Num (I32 n)) -> 
      (* Printf.printf "\n%d %s\n" (sz) (Expression.to_string v); *)
      Hashtbl.replace h.cache (addr, idx') (sz, v)
    (* Store in symbolic index *)
    | _ -> Hashtbl.clear h.cache);
    store_n h addr idx' sz v;
    [ (h, []) ]


  let load_bytes (ops : op list) (sz : int) (v : Expression.t): 
    Expression.t list =
    let rec loop ops n acc =
      if n == sz then acc
      else
        match ops with               (* change to I64 *)
        | [] -> Expression.Extract (Val (Num (I32 0l)), 1, 0) :: acc
        | (offset, v) :: op_list' -> loop op_list' (n + 1) (v :: acc)
    in
    loop ops 1 [v]
  
  
  let rec load_n (check_sat_helper : Expression.t -> bool) (ops : op list) (idx : Expression.t) (sz : int) :
    Expression.t list =
    match ops with
    | [] -> [ Extract (Val (Num (I32 0l)), sz, 0) ]
    | (offset, v) :: op_list' ->
        let expr = Expression.Relop (I32 I32.Eq, idx, offset) in
        (* Printf.printf "\n%s\n" (Expression.to_string expr); *)
        if not (check_sat_helper expr) then
             load_bytes op_list' sz v
        else load_n check_sat_helper op_list' idx sz


  let load (expr_to_value : (expr -> expr -> Num.t)) (check_sat_helper : Expression.t -> bool) 
    (h : t) (addr : address) (idx : Expression.t) (o : int32) (sz : int) (ty : num_type) 
    (is_packed : bool) : 
    (t * Expression.t * Expression.t list) list =
    (* Printf.printf "\n\n%s\n\n" (to_string h); *)
    let aux = Expression.Binop (I32 I32.Add, idx, Val (Num (I32 o))) in
    let aux = Expression.simplify aux in
    let v = match Hashtbl.find_opt h.cache (addr, aux) with
    | Some (sz', v) -> 
      (* Printf.printf "\n %s \n" (Expression.to_string v); *)
      if sz' == sz then Some v 
      else (
        if sz' > sz then
          Some (Extract (v, sz, 0))
        else None)
    | None -> None 
    in
    match v with
    (* In cache *)
    | Some v -> (* Printf.printf "\nCache!\n"; *) [ h, v, [] ] 
    (* Not in cache *)
    | None -> (* Printf.printf "\nNOT CACHE!\n"; *)
      let arr' = Hashtbl.find h.mem addr in
      let _, ops = arr' in
      let idx' = Expression.Binop (I32 I32.Add, aux, Val (Num (I32 (Int32.of_int (sz-1))))) in
      let idx' = Expression.simplify idx' in
      let exprs = load_n check_sat_helper ops idx' sz in
      let v = concat_exprs exprs ty sz is_packed in
      Hashtbl.replace h.cache (addr, aux) (sz, v);
      [ h, v, [] ]
      

  let from_heap (h : Concolic.Heap.t) : t =
    failwith "not implemented"


  let clone (h : t) : t * t = 
    let h_copy = Hashtbl.copy h.mem in
    let c_copy = Hashtbl.copy h.cache in
    ( h, { mem = h_copy; cache = c_copy } )


  let to_heap (h : t) (expr_to_value : Expression.t -> Num.t) :
      Concolic.Heap.t =
    failwith "not implemented"


  let alloc (check_sat_helper : Expression.t option -> bool) (h : t)  
    (b : address) (sz : Expression.t) (binds : (Symbol.t * Value.t) list): 
    (t * int32 * Expression.t list) list =    Hashtbl.replace h.mem b (sz, []);
    [ ( h, b, [] ) ]


  let free (h : t) (addr : address) : unit =
    Hashtbl.remove h.mem addr


  let check_bound (h : t) (addr : address) : bool =
    Hashtbl.mem h.mem addr


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
    (match Hashtbl.find_opt h.mem addr with
    | Some (block_sz, _)  -> 
        (match block_sz with
        | Val (Num (I64 block_sz')) -> is_within (Val (Num (I32 (Int64.to_int32 block_sz')))) idx o sz
        | Val (Num (I32 _))
        | _ -> is_within block_sz idx o sz)
        (* | _ -> Printf.printf "\n\n%s\n\n" (Expression.to_string block_sz);
          failwith ("InternalError: OpList.in_bounds, size not an integer or SymPtr")) *)
    | _ -> failwith ("InternalError: OpList.in_bounds, accessed OpList is not in the heap"))

end