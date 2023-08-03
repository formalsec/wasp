type bug = Overflow | UAF | InvalidFree

exception BugException of bug * Interpreter.Source.region * string

let string_of_bug : bug -> string = function
  | Overflow -> "Overflow"
  | UAF -> "Use After Free"
  | InvalidFree -> "Invalid Free"
