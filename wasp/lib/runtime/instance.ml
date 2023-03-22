open Types

type module_inst =
{
  types : func_type list;
  funcs : func_inst list;
  tables : table_inst list;
  memories : memory_inst list;
  globals : global_inst list;
  exports : export_inst list;
}

and func_inst = module_inst ref Func.t
and table_inst = Table.t
and memory_inst = Memory.t
and global_inst = Global.t
and export_inst = Ast.name * extern

and extern =
  | ExternFunc of func_inst
  | ExternTable of table_inst
  | ExternMemory of memory_inst
  | ExternGlobal of global_inst

type Table.elem += FuncElem of func_inst


(* Auxiliary functions *)

let clone (m: module_inst): module_inst =
  let types = m.types in
  let funcs = m.funcs in
  let tables = m.tables in
  let memories = m.memories in
  let globals = m.globals in
  let exports = m.exports in
  {
    types = types;
    funcs = funcs;
    tables = tables;
    memories = memories;
    globals = globals;
    exports = exports;
  }

let empty_module_inst =
  { types = []; funcs = []; tables = []; memories = [];
    globals = []; exports = [] }

let extern_type_of = function
  | ExternFunc func -> ExternFuncType (Func.type_of func)
  | ExternTable tab -> ExternTableType (Table.type_of tab)
  | ExternMemory mem -> ExternMemoryType (Memory.type_of mem)
  | ExternGlobal glob -> ExternGlobalType (Global.type_of glob)

let export inst name =
  try Some (List.assoc name inst.exports) with Not_found -> None

let modulecpy (m : module_inst) : module_inst =
  let new_globals = List.map Global.globcpy m.globals in
  let new_memories = List.map Memory.memcpy m.memories in
  { m with memories = new_memories; globals = new_globals }

let set_globals (m : module_inst) (vals : Values.value list) : unit =
  List.iter2 (fun glob v -> Global.safe_store glob v) m.globals vals
