open Encoding
open Expression
open Concolic
open Interpreter.Types
open Interpreter.Instance

type global = { content : Expression.t; mut : mutability }
type global_map = (int32, global) Hashtbl.t
type t = global_map

let clone_globals (map : t) : t = Hashtbl.copy map

exception Type
exception NotMutable

let to_globals (sym_g : t) (expr_to_value : Expression.t -> Num.t) :
    Concolic.Globals.t =
  let sym_to_conc ((idx, g) : int32 * global) : int32 * (Num.t * Expression.t) =
    let c = expr_to_value g.content in
    (idx, (c, g.content))
  in
  let g = Concolic.Globals.create () in
  let sym_seq = Hashtbl.to_seq sym_g in
  let conc_seq = Seq.map sym_to_conc sym_seq in
  Concolic.Globals.add_seq g conc_seq;
  g

let alloc (GlobalType (t, mut)) v =
  if type_of v <> Evaluations.to_num_type t then raise Type;
  { content = v; mut }

let from_list (global_inst_list : global_inst list) : t =
  let tup_list =
    List.mapi
      (fun idx glob ->
        ( Int32.of_int idx,
          let value = Interpreter.Global.load glob in
          let typ = Interpreter.Global.type_of glob in
          let expr = Num (Evaluations.of_value value) in
          alloc typ expr ))
      global_inst_list
  in
  let seq = List.to_seq tup_list in
  Hashtbl.of_seq seq

let type_of glob =
  let t =
    match type_of glob.content with
    | `I32Type -> I32Type
    | `I64Type -> I64Type
    | `F32Type -> F32Type
    | `F64Type -> F64Type
    | _ -> assert false
  in
  GlobalType (t, glob.mut)

let load (map : global_map) (x : int32) : Expression.t =
  let g = Hashtbl.find map x in
  g.content

let store (map : global_map) (x : int32) (ex : Expression.t) : unit =
  match Hashtbl.find_opt map x with
  | Some g ->
      if g.mut <> Mutable then raise NotMutable;
      if Expression.type_of ex <> Expression.type_of g.content then raise Type;
      Hashtbl.replace map x { g with content = ex }
  | None ->
      (* TODO: fix mutability/initialization *)
      let g = { content = ex; mut = Mutable } in
      Hashtbl.replace map x g
