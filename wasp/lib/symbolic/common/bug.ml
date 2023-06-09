type bug = Overflow | UAF | InvalidFree | OOB

exception BugException of bug * Interpreter.Source.region * string

let string_of_bug : bug -> string = function
  | Overflow -> "Out Of Bounds Write"
  | UAF -> "Use After Free"
  | InvalidFree -> "Invalid Free"
  | OOB -> "Out Of Bounds Read"
