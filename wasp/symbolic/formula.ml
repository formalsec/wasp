open Symvalue

type formula =
  | True
  | False
  | Not   of formula 
  | And   of formula * formula
  | Or    of formula * formula
  | Relop of Symvalue.sym_expr

type t = formula

let rec negate (f : formula) : formula =
  match f with
  | True  -> False
  | False -> True
  | Not c -> c
  | And (c1, c2) -> Or  (negate c1, negate c2)
  | Or  (c1, c2) -> And (negate c1, negate c2)
  | Relop e -> Relop (Symvalue.negate_relop e)

let conjuct (conds : formula list) : formula =
  assert (not (conds = []));
  let rec loop (acc : t) = function
    | []     -> acc
    | h :: t -> loop (And (acc, h)) t
  in loop (List.hd conds) (List.tl conds)

let rec to_string (f : formula) : string =
  match f with
  | True  -> "True"
  | False -> "False"
  | Not c -> "(¬ " ^ (to_string c) ^ ")"
  | And (c1, c2) -> 
      let c1_str = to_string c1
      and c2_str = to_string c2 in
      "(" ^ c1_str ^ " /\\ " ^ c2_str ^")"
  | Or (c1, c2) ->
      let c1_str = to_string c1
      and c2_str = to_string c2 in
      "(" ^ c1_str ^ " \\/ " ^ c2_str ^")"
  | Relop e -> Symvalue.pp_to_string e

let rec length (e : formula) : int =
  match e with
  | True | False | Relop _ -> 1
  | Not c        -> 1 + (length c)
  | And (c1, c2) -> 1 + (length c1) + (length c2)
  | Or  (c1, c2) -> 1 + (length c1) + (length c2)

let to_formula (pc : sym_expr list) : formula =
  conjuct (List.map (fun e -> Relop e) pc)
