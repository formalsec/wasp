open Encoding
open Value
open Expression
open Types
open Operators

module ArrayITE : Block.M = struct
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


  let filter_indexes (block : Expression.t list) (o : int) (sz : int): Expression.t list =
    let rec loop o sz i l : Expression.t list =
      if i >= o+sz then l
      else 
        loop o sz (i+1) (List.tl l)
    in
    loop o sz 0 block

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
    

  let store_n_symb (h : t) (addr : address) (idx : int) (e : expr) (n : int) 
    (v : Expression.t) : unit =
    let block = Hashtbl.find h addr in
    let rec loop mem a i n x =
      if n > i then (
        let old_expr = Array.get (block) (idx + i) in
        let x' = 
          match x with 
          | Extract (_, _, _) -> x 
          | _ -> Expression.Extract (x, i + 1, i)
        in
        let x'' = Expression.Triop (Bool B.ITE, e, x', old_expr)
        in
        store_byte mem a (idx+i) x'';
        loop mem a (i + 1) n x)
    in
    loop h addr 0 n v

  let store (expr_to_value : (expr -> expr -> Num.t)) (check_sat_helper : Expression.t -> bool)
    (h : t) (addr : address) (idx : Expression.t) 
    (o : int32) (v : Expression.t)  (sz : int) :
    (t * Expression.t list) list =
    let idx = Expression.simplify idx in
    match idx with
    (* Store in concrete index *)
    | Val (Num (I32 idx')) -> 
      store_n h addr (Int32.to_int o) (Int32.to_int idx') sz v;
      [ ( h, [] ) ]
    (* Store in symbolic index *)
    | _ -> 
      let o = Val (Num (I32 o)) in
      let index = Expression.Binop (I32 I32.Add, idx, o) in
      let block = Hashtbl.find h addr in
      Core.Array.iteri ~f:(fun j old_expr ->
        let e = Expression.Relop (I32 I32.Eq, index, Val (Num (I32 (Int32.of_int j)))) in
        if not (check_sat_helper e) then 
          store_n_symb h addr j e sz v
        else ()) block;
      [ ( h, [] ) ]


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
    (* Printf.printf "\n\n%s\n\n" (to_string h); *)
    
    match idx with
    (* Load in concrete index *)
    | Val (Num (I32 idx')) -> 
      let exprs = load_n h addr (Int32.to_int o) (Int32.to_int idx') sz in
      let v = concat_exprs exprs ty sz is_packed in
      [ ( h, v, [] ) ]
    (* Load in symbolic index, makes an ITE with all possible values *)
    | _ -> 
      let block = Hashtbl.find h addr in
      let o' = Val (Num (I32 o)) in
      let index = Expression.Binop (I32 I32.Add, idx, o') in
      (* this is a bit of a mess.. could probably be cleaned and optimized *)
      let block = Array.of_list (filter_indexes (Array.to_list block) (Int32.to_int o) sz) in
      let aux = Array.of_list (List.filteri (fun index' _ ->
                let e = Expression.Relop (I32 I32.Eq, index, Val (Num (I32 (Int32.of_int index')))) in
                if check_sat_helper e then false else true)
                (Array.to_list (Core.Array.mapi ~f:(fun j e -> (
                  Expression.Relop (I32 I32.Eq, index, Val (Num (I32 (Int32.of_int j)))), 
                  concat_exprs (load_n h addr (Int32.to_int o) (j) sz) ty sz is_packed
                )) block )))
      in
      let f = fun (bop, e) l ->
              (match e with
              | Expression.Triop (_, a, b, _) ->
                  let e = Expression.Binop (Bool B.And, bop, a) in 
                  Expression.Triop (Bool B.ITE, e, b, l)
              | _ ->  Expression.Triop (Bool B.ITE, bop, e, l))
      in
      let v = Array.fold_right f aux (Val (Num (I32 (0l)))) in
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


  let alloc (check_sat_helper : Expression.t option -> bool) (h : t)  
    (b : address) (sz : Expression.t) (binds : (Symbol.t * Value.t) list): 
    (t * int32 * Expression.t list) list =    match sz with
    (* concrete alloc *)
    |  Val (Num (I32 sz)) -> 
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
      | _ -> failwith ("InternalError: ArrayITE.in_bounds, accessed array is not in the heap"))
end