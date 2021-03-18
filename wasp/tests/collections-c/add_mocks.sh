for t in $(find "./_build/for-wasp" -name  "*.wat"); do
  echo "tranforming $t"
  sed -i'' -e 's/(elem (;0;) (i32.const 1) func/(elem (;0;) (i32.const 1)/' $t
  comby '(func $assume (type :[x]) (param i32))' '(func $assume (type :[x]) (param i32)
    local.get 0
    sym_assume)' $t -i > /dev/null 2>&1
  comby '(func $assert (type :[x]) (param i32))' '(func $assert (type :[x]) (param i32)
    local.get 0
    sym_assert)' $t -i > /dev/null 2>&1
  comby '(func $dyn_sym_int32 (type :[x]) (param i32) (result i32)
    local.get 0)' '(func $dyn_sym_int32 (type :[x]) (param i32) (result i32)
    local.get 0
    dyn_sym_int32)' $t -i > /dev/null 2>&1
done
