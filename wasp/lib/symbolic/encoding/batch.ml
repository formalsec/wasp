open Z3
open Expression
open Formula
open Interpreter
open Interpreter.Types
open Interpreter.Values
open Common

type t = { solver : s; pc : path_conditions ref }
and s = Solver.solver

let time_solver = ref 0.0

let time_call f acc =
  let start = Sys.time () in
  let ret = f () in
  acc := !acc +. (Sys.time () -. start);
  ret

let create () = { solver = Solver.mk_solver ctx None; pc = ref [] }
let interrupt () = Tactic.interrupt ctx
let clone (s : t) : t = { s with pc = ref !(s.pc) }
let add (s : t) (e : sym_expr) : unit = s.pc := e :: !(s.pc)

let formulas_to_smt2_file =
  let counter = ref 0 in
  let file () : string =
    let () = incr counter in
    Printf.sprintf "query-%d.smt2" !counter
  in
  fun f status ->
    Params.set_print_mode ctx Z3enums.PRINT_SMTLIB2_COMPLIANT;
    let query_out = Filename.concat !Flags.output "queries" in
    let query_file = Filename.concat query_out (file ()) in
    Io.safe_mkdir query_out;
    Io.save_file query_file
      (SMT.benchmark_to_smtstring ctx query_file "" status "" (List.tl f)
         (List.hd f))

let check (s : t) (es : sym_expr list) : bool =
  let es' = es @ !(s.pc) in
  let formulas' = List.map encode_formula (to_formulas es') in
  let sat = time_call (fun () -> Solver.check s.solver formulas') time_solver in
  let status, b =
    match sat with
    | Solver.SATISFIABLE -> ("sat", true)
    | Solver.UNSATISFIABLE -> ("unsat", false)
    | Solver.UNKNOWN ->
        if !Flags.queries then formulas_to_smt2_file formulas' "unknown";
        failwith ("unknown: " ^ Solver.get_reason_unknown s.solver)
  in
  if !Flags.queries then formulas_to_smt2_file formulas' status;
  b

let fork (s : t) (e : sym_expr) : bool * bool =
  (check s [ e ], check s [ negate_relop e ])

let value_of_const model (c, t) =
  let interp = Model.eval model (encode_sym_expr c) true in
  let f e =
    let v =
      if BitVector.is_bv e then int64_of_bv e
      else
        let ebits = FloatingPoint.get_ebits ctx (Expr.get_sort e)
        and sbits = FloatingPoint.get_sbits ctx (Expr.get_sort e) in
        int64_of_fp e ebits (sbits - 1)
    in
    match t with
    | Types.I32Type -> I32 (Int64.to_int32 v)
    | Types.I64Type -> I64 v
    | Types.F32Type ->
        F32 (F32.of_float (Int32.float_of_bits (Int64.to_int32 v)))
    | Types.F64Type -> F64 (F64.of_float (Int64.float_of_bits v))
  in
  Option.map f interp

let get_model (s : t) : Model.model =
  match Solver.get_model s.solver with
  | Some m -> m
  | None -> assert false (* should not happen after sat check *)

let model (s : t) : Model.model =
  assert (check s []);
  get_model s

let model_binds (model : Model.model) (vars : (string * value_type) list) :
    (string * value) list =
  List.fold_left
    (fun a (x, t) ->
      let v = value_of_const model (to_symbolic t x, t) in
      Batteries.Option.map_default (fun v' -> (x, v') :: a) a v)
    [] vars

let value_binds (s : t) (vars : (string * value_type) list) :
    (string * value) list =
  let model = model s in
  model_binds model vars

let string_binds s vars = []
