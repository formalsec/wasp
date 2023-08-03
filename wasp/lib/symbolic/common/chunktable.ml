open Encoding
open Bug

type t = (int32, int32) Hashtbl.t

let replace (ct : t) (address : int32) (size : int32) =
  Hashtbl.replace ct address size

let copy (ct : t) = Hashtbl.copy ct
let create () = Hashtbl.create Interpreter.Flags.hashtbl_default_size
let find (ct : t) (low : int32) = Hashtbl.find ct low
let find_opt (ct : t) (low : int32) = Hashtbl.find_opt ct low
let mem (ct : t) (base : int32) = Hashtbl.mem ct base
let remove (ct : t) (base : int32) = Hashtbl.remove ct base

let check_access (ct : t) (base_ptr : int32) (ptr : Num.t) (offset : int32) =
  let low = base_ptr in
  match find_opt ct low with
  | Some chunk_size ->
      let high = Int64.(add (of_int32 low) (of_int32 chunk_size)) in
      let ptr_i64 =
        Int64.of_int32
          (Interpreter.Values.I32Value.of_value (Evaluations.to_value ptr))
      in
      let ptr_val = Int64.(add ptr_i64 (of_int32 offset)) in
      (* ptr_val \notin [low, high[ => overflow *)
      if ptr_val < Int64.of_int32 low || ptr_val >= high then Some Overflow
      else None
  | None -> Some UAF

let alloc (ct : t) (base : int32) (sz : int32) = replace ct base sz
