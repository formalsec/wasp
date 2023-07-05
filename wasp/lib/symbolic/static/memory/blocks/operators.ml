open Encoding
open Value
open Expression
open Types


let concat_exprs (exprs : Expression.t list) (ty : num_type) 
  (sz : int) (is_packed : bool) : Expression.t =
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
  v