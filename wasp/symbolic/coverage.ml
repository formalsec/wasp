open Ast
open Source
open Instance
open Batteries

(* This module is just to help calculate the coverage of 
 * the AWS Encryption SDK, it is not guaranteed to work 
 * with other programs.
 *)

let lines : int ref = ref 0
let visited : int list ref = ref []
let funcs : (string, int32) Hashtbl.t = Hashtbl.create 32

let ign = [
  (* WASP *)
  "$assume";
  "$assert";
  "$sym_int";
  "$sym_long";
  "$sym_float";
  "$sym_double";
  "$alloc";
  "$dealloc";
  "$is_symbolic";
  "$free";
  "$IFG";
  "$__logor";
  "$__logand";
  "$__ternary";
  (* other functions *)
  "$assume_abort_if_not";
  "$assume_cycle_if_not";
  "$__VERIFIER_nondet_bool";
  "$__VERIFIER_nondet_char";
  "$__VERIFIER_nondet_uchar";
  "$__VERIFIER_nondet_short";
  "$__VERIFIER_nondet_ushort";
  "$__VERIFIER_nondet_int";
  "$__VERIFIER_nondet_uint";
  "$__VERIFIER_nondet_long";
  "$__VERIFIER_nondet_ulong";
  "$__VERIFIER_nondet_float";
  "$__VERIFIER_nondet_double";
]

let record_loc (path : string) : unit =
  lines := File.count_lines path

let record_line (id : int) : unit =
  if not (List.memq id !visited) then
    visited := id :: !visited

let save_func (name : string) (id : int32) : unit =
  (* print_endline (name ^ "->" ^ (Int32.to_string id)) *)
  if List.mem name ign then
    Hashtbl.add funcs name id

let count_func (id : int32) (inst : module_inst ref) : int =
  let func = Lib.List32.nth !inst.funcs id in
  let f = match func with Func.AstFunc (_, _, f) -> f | _ -> failwith "HostFunc" in
  (List.length f.it.body) + (if (List.length f.it.locals) > 0 then 1 else 0) + 1

let calculate_cov (inst : module_inst ref) (n_lines : int) : float =
  let ign_lines = Hashtbl.fold (
    fun a b acc ->
      print_endline ("ignoring " ^ a);
      acc + (count_func b inst) 
  ) funcs 0 in
  let visited_len = List.length !visited in
  (float_of_int visited_len) /. (float_of_int (!lines - ign_lines - n_lines))
