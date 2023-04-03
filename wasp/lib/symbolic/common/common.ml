module Counter = Counter
module RandArray = RandArray
module Evaluations = Evaluations

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
