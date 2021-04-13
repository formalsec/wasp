for t in $(find "./_build/for-wasp" -name  "*.wat"); do
  echo "tranforming $t"
  sed -i'' -e 's/(elem (;0;) (i32.const 1) func/(elem (;0;) (i32.const 1)/' $t
  comby 'call $assume' 'sym_assume' $t -i > /dev/null 2>&1
  comby 'call $assert' 'sym_assert' $t -i > /dev/null 2>&1
  comby 'call $sym_int' 'sym_int' $t -i > /dev/null 2>&1
done
