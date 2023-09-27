let py_module = lazy (Py.Import.import_module "instrumentor")
let import_module () = Lazy.force py_module

let instrument data includes =
  let callable = Py.Module.get (import_module ()) "instrument" in
  let kwargs =
    [ ("data", Py.String.of_string data)
    ; ("includes", Py.List.of_list @@ List.map Py.String.of_string includes)
    ] in
  Py.String.to_string
  @@ Py.Callable.to_function_with_keywords callable [||] kwargs
