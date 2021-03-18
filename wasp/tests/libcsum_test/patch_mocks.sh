comby '(func $assume (type :[x]) (param i32)
  local.get 0
  drop)' '(func $assume (type :[x]) (param i32)
  local.get 0
  sym_assume)' $t -i > /dev/null 2>&1
comby '(func $assert (type :[x]) (param i32)
  local.get 0
  drop)' '(func $assert (type :[x]) (param i32)
  local.get 0
  sym_assert)' $t -i > /dev/null 2>&1
comby '(func $dyn_sym_int32 (type :[x]) (param i32) (result i32)
  local.get 0
  drop
  i32.const 0)' '(func $dyn_sym_int32 (type :[x]) (param i32) (result i32)
  local.get 0
  dyn_sym_int32)' $t -i > /dev/null 2>&1
