open Prelude
open Interpreter
open Instance
open Types

let i32_symbol _env = assert false

let lookup name t =
  match (Interpreter.Utf8.encode name, t) with
  | "i32_symbol", ExternFuncType t -> ExternFunc (Func.alloc_host t i32_symbol)
  | _ -> Fmt.failwith "Not found"
