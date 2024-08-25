open Prelude

type bug =
  | Overflow
  | UAF
  | InvalidFree

exception BugException of bug * Interpreter.Source.region * string

let pp fmt = function
  | Overflow -> Fmt.string fmt "Overflow"
  | UAF -> Fmt.string fmt "Use After Free"
  | InvalidFree -> Fmt.string fmt "Invalid Free"
