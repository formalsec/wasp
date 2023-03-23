open Z3
open Interpreter
open Interpreter.Types
open Interpreter.Values
open Common

exception Unknown

let time_solver = ref 0.0

let time_call f acc =
  let start = Sys.time () in
  let ret = f () in
  acc := !acc +. ((Sys.time ()) -. start);
  ret

type s = Solver.solver
type t = {
  solver : s;
  pc : Expression.path_conditions ref;
}

let create () : t =
  {
    solver = Solver.mk_solver ctx None;
    pc = ref [];
  }

let clone (e : t) : t =
  { solver = Solver.translate e.solver ctx; pc = ref !(e.pc) }

let add (e : t) (c : Expression.t):  unit =
  e.pc := c :: !(e.pc);
  let ec = encode_sym_expr ~bool_to_bv:false c in
  Solver.add e.solver [ec]

let check (e : t) (vs : Expression.t list) : bool =
  let vs' = List.map (encode_sym_expr ~bool_to_bv:false) vs in
  let b =
    let sat =
      time_call (fun () -> Solver.check e.solver vs') time_solver
    in
    match sat with
    | Solver.SATISFIABLE -> true
    | Solver.UNKNOWN ->
      failwith ("unknown: " ^ (Solver.get_reason_unknown e.solver)) (* fail? *)
    | Solver.UNSATISFIABLE -> false
  in
  b

let fork (e : t) (co : Expression.t) : bool * bool =
  let negated_co = Expression.negate_relop co in
  (check e [ co ]), (check e [ negated_co ])

let value_of_const model c =
  let interp = Model.get_const_interp_e model (encode_sym_expr c) in
  let f e =
    let v =
      if BitVector.is_bv e then int64_of_bv e
      else
        let ebits = FloatingPoint.get_ebits ctx (Expr.get_sort e)
        and sbits = FloatingPoint.get_sbits ctx (Expr.get_sort e) in
        int64_of_fp e ebits (sbits - 1)
    in
    match Expression.type_of c with
    | I32Type -> I32 (Int64.to_int32 v)
    | I64Type -> I64 v
    | F32Type -> F32 (F32.of_bits (Int64.to_int32 v))
    | F64Type -> F64 (F64.of_bits v)
  in
  Option.map f interp

(** fails if solver isn't currently SAT *)
let model (e : t) : Model.model =
  assert (check e []);
  Option.get (Solver.get_model e.solver)

(** fails if solver isn't currently SAT *)
let value_binds (e : t) vars : (string * value) list =
  let m = model e in
  List.fold_left
    (fun a (x, t) ->
      let v = value_of_const m (Expression.to_symbolic t x) in
      Batteries.Option.map_default (fun v' -> (x, v') :: a) (a) v)
    [] vars

(** fails if solver isn't currently SAT *)
let string_binds (e : t) vars :
    (string * string * string) list =
  let m = model e in
  List.map
    (fun const ->
      let sort = Sort.to_string (FuncDecl.get_range const)
      and name = Symbol.to_string (FuncDecl.get_name const)
      and interp =
        Batteries.Option.map_default Expr.to_string ""
          (Model.get_const_interp m const)
      in
      (sort, name, interp))
    (Model.get_const_decls m)
