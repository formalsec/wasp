#!/bin/sh

TEST=$1

echo "Patching $TEST"
sed -i'' -e 's/\<call $assume\>/sym_assume/' $TEST
sed -i'' -e 's/\<call $assert\>/sym_assert/' $TEST
sed -i'' -e 's/call $sym_int/sym_int/' $TEST
sed -i'' -e 's/call $sym_long/sym_long/' $TEST
sed -i'' -e 's/call $sym_float/sym_float/' $TEST
sed -i'' -e 's/call $sym_double/sym_double/' $TEST
sed -i'' -e 's/call $is_symbolic/is_symbolic/' $TEST
sed -i'' -e 's/\<call $alloc\>/alloc/' $TEST
sed -i'' -e 's/\<call $free\>/free/' $TEST
sed -i'' -e 's/\<call $dealloc\>/free/' $TEST
sed -i'' -e 's/(elem (;0;) (i32.const 1) func/(elem (;0;) (i32.const 1)/' $TEST
sed -i'' -e 's/anyfunc/funcref/' $TEST
