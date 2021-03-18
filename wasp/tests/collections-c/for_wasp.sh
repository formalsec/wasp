rm -rf for-wasp
cp -R for-gillian for-wasp

for source in $(find "./for-wasp" -name "*.c") $(find "./for-wasp" -name "*.h"); do
  echo "transforming $source"
  sed -i'' -e 's/#include <gillian-c\/gillian-c.h>/#include "mockups.h" /' $source
  comby "int :[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);" \
    "int :[x] = dyn_sym_int32(':[x]');" -d $(dirname $source) $(basename $source) -i
  comby "char :[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);" \
    "int :[x] = dyn_sym_int32(':[x]');" -d $(dirname $source) $(basename $source) -i
  comby "char :[[x]] = (char)__builtin_annot_intval(\"symb_int\", :[[x]]);" \
    "int :[x] = dyn_sym_int32(':[x]');" -d $(dirname $source) $(basename $source) -i
  comby ':[[type]] X = (:[[type]])__builtin_annot_intval("symb_int", :[[x]])' \
    ":[type] :[x] = dyn_sym_int32(':[x]');" -d $(dirname $source) $(basename $source) -i
  comby ":[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);" \
    ":[x] = dyn_sym_int32(':[x]');" -d $(dirname $source) $(basename $source) -i
  comby '*:[[x]] = __builtin_annot_intval("symb_int", *:[[x]]);' \
    ":[x] = dyn_sym_int32(':[x]');" -d $(dirname $source) $(basename $source) -i

  comby 'ASSERT(:[assertion]);' 'assert(:[assertion]);' \
    -d $(dirname $source) $(basename $source) -i
  comby 'ASSUME(:[assertion]);' 'assume(:[assertion]);' \
    -d $(dirname $source) $(basename $source) -i
  comby 'ASSUME (:[assertion]);' 'assume(:[assertion]);' \
    -d $(dirname $source) $(basename $source) -i
done
