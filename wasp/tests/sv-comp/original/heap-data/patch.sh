for t in $(find "./_build" -name "*.wat"); do
  echo "patching $t"
  sed -i'' -e 's/\<call $assume\>/sym_assume/' $t
  sed -i'' -e 's/\<call $assert\>/sym_assert/' $t
  sed -i'' -e 's/call $sym_int/sym_int/' $t
  sed -i'' -e 's/call $sym_float/sym_float/' $t
done
