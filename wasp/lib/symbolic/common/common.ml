module Counter = Counter
module RandArray = RandArray
module Chunktable = Chunktable
module Evaluations = Evaluations
module Globals = Globals
module Bug = Bug
module Link = Interpreter.Error.Make ()
module Trap = Interpreter.Error.Make ()
module Crash = Interpreter.Error.Make ()
module Exhaustion = Interpreter.Error.Make ()

exception Link = Link.Error
exception Trap = Trap.Error
exception Crash = Crash.Error
exception Exhaustion = Exhaustion.Error

module type WorkList = sig
  type 'a t

  exception Empty

  val create : unit -> 'a t
  val push : 'a -> 'a t -> unit
  val pop : 'a t -> 'a
  val add_seq : 'a t -> 'a Seq.t -> unit
  val is_empty : 'a t -> bool
  val length : 'a t -> int
end

let count (init : int) : unit -> int =
  let next = ref init in
  let next () =
    let n = !next in
    next := n + 1;
    n
  in
  next

let test_case_cntr = count 0

let write_test_case ?(witness = false) test_data : unit =
  let out_dir = Filename.concat !Interpreter.Flags.output "test_suite" in
  if not (test_data = "[]") then
    let i = test_case_cntr () in
    let filename =
      if witness then Printf.sprintf "%s/witness_%05d.json" out_dir i
      else Printf.sprintf "%s/test_%05d.json" out_dir i
    in
    Interpreter.Io.save_file filename test_data

let numeric_error at = function
  | Evaluations.UnsupportedOp m -> m ^ ": unsupported operation"
  | Interpreter.Numeric_error.IntegerOverflow -> "integer overflow"
  | Interpreter.Numeric_error.IntegerDivideByZero -> "integer divide by zero"
  | Interpreter.Numeric_error.InvalidConversionToInteger ->
      "invalid conversion to integer"
  | Interpreter.Eval_numeric.TypeError (i, v, t) ->
      Crash.error at
        ("type error, expected "
        ^ Interpreter.Types.string_of_value_type t
        ^ " as operand " ^ string_of_int i ^ ", got "
        ^ Interpreter.Types.string_of_value_type (Interpreter.Values.type_of v)
        )
  | exn -> raise exn

let logger (logs : (int * int * int) list ref) (get_finished : unit -> int) :
    unit =
  let cnt = ref 0 in
  let handler (i : int) : unit =
    print_endline "awoke";
    let pcs = get_finished () in
    let mem_size =
      let open Gc in
      let gc_stats = quick_stat () in
      gc_stats.heap_words * 8
    in
    logs := (!cnt, pcs, mem_size) :: !logs;
    cnt := !cnt + 1;
    ignore (Unix.alarm 1)
  in
  Sys.(set_signal sigalrm (Signal_handle handler));
  ignore (Unix.alarm 1)

let print_logs (logs : (int * int * int) list) : unit =
  let log_dir = Filename.concat !Interpreter.Flags.output "logs" in
  Interpreter.Io.safe_mkdir log_dir;
  let log_file =
    Filename.concat
      (Filename.concat !Interpreter.Flags.output "logs")
      "pcs_mem.csv"
  in
  let logs_strings =
    List.map
      (fun (t, pcs, mem_size) -> Printf.sprintf "%d,%d,%d\n" t pcs mem_size)
      logs
  in
  let logs_string = String.concat "" logs_strings in
  Interpreter.Io.save_file log_file logs_string
