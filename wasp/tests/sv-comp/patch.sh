for t in $(find "$1/_build" -name "*.wat"); do
  echo "patching $t"
  sed -i'' -e 's/\<call $assume\>/sym_assume/' $t
  sed -i'' -e 's/\<call $assert\>/sym_assert/' $t
  sed -i'' -e 's/call $sym_int/sym_int/' $t
  sed -i'' -e 's/call $sym_long/sym_long/' $t
  sed -i'' -e 's/call $sym_float/sym_float/' $t
  sed -i'' -e 's/call $sym_double/sym_double/' $t
  sed -i'' -e 's/call $is_symbolic/is_symbolic/' $t
  sed -i'' -e 's/\<call $alloc\>/alloc/' $t
  sed -i'' -e 's/\<call $free\>/free/' $t
  sed -i'' -e 's/\<call $dealloc\>/free/' $t
  sed -i'' -e 's/(elem (;0;) (i32.const 1) func/(elem (;0;) (i32.const 1)/' $t
  sed -i'' -e 's/anyfunc/funcref/' $t
done
