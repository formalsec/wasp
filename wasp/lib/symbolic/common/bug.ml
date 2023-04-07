type bug = Overflow | UAF | InvalidFree

exception BugException of bug * Interpreter.Source.region * string
