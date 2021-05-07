for t in $(find "./_build/for-wasp" -name  "*.wat"); do
  echo "tranforming $t"
  sed -i'' -e 's/(elem (;0;) (i32.const 1) func/(elem (;0;) (i32.const 1)/' $t
  sed -i'' -e 's/\<call $assume\>/sym_assume/' $t
  sed -i'' -e 's/\<call $assert\>/sym_assert/' $t
  sed -i'' -e 's/\<call $sym_int\>/sym_int/' $t
  sed -i'' -e 's/\<call $alloc\>/alloc/' $t
  sed -i'' -e 's/\<call $free\>/free/' $t
  sed -i'' -e 's/\<call $dealloc\>/free/' $t
done
