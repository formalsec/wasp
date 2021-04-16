"""
rm -rf for-wasp
cp -R for-gillian for-wasp

for source in $(find "./for-wasp" -name "*.c") $(find "./for-wasp" -name "*.h"); do
  echo "transforming $source"
  sed -i'' -e 's/#include <gillian-c\/gillian-c.h>/#include "mockups.h" /' $source
  comby "int :[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);" \
    "int :[x] = sym_int(\":[x]\", 32);" -d $(dirname $source) $(basename $source) -i
  comby "char :[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);" \
    "int :[x] = sym_int(\":[x]\", 32);" -d $(dirname $source) $(basename $source) -i
  comby "char :[[x]] = (char)__builtin_annot_intval(\"symb_int\", :[[x]]);" \
    "int :[x] = sym_int(\":[x]\", 32);" -d $(dirname $source) $(basename $source) -i
  comby ':[[type]] X = (:[[type]])__builtin_annot_intval("symb_int", :[[x]])' \
    ":[type] :[x] = sym_int(\":[x]\", 32);" -d $(dirname $source) $(basename $source) -i
  comby ":[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);" \
    ":[x] = sym_int(\":[x]\", 32);" -d $(dirname $source) $(basename $source) -i
  comby '*:[[x]] = __builtin_annot_intval("symb_int", *:[[x]]);' \
    ":[x] = sym_int(\":[x]\", 32);" -d $(dirname $source) $(basename $source) -i

  comby 'ASSERT(:[assertion]);' 'assert(:[assertion]);' \
    -d $(dirname $source) $(basename $source) -i
  comby 'ASSUME(:[assertion]);' 'assume(:[assertion]);' \
    -d $(dirname $source) $(basename $source) -i
  comby 'ASSUME (:[assertion]);' 'assume(:[assertion]);' \
    -d $(dirname $source) $(basename $source) -i
done
"""

import shutil
import glob, comby as cby

shutil.rmtree('for-wasp')
shutil.copytree('for-gillian', 'for-wasp')

srcs = glob.glob('./for-wasp/**/*.c', recursive=True)
srcs = srcs + glob.glob('./for-wasp/**/*.h', recursive=True)

patterns = [
        ('#include <gillian-c/gillian-c.h>', '#include "mockups.h"'),
        ("int :[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);", \
                "int :[x] = sym_int(\":[x]\");"),
        ("char :[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);", \
                "int :[x] = sym_int(\":[x]\");"),
        ("char :[[x]] = (char)__builtin_annot_intval(\"symb_int\", :[[x]]);", \
                "int :[x] = sym_int(\":[x]\");"),
        (':[[type]] X = (:[[type]])__builtin_annot_intval("symb_int", :[[x]])', \
                ":[type] :[x] = sym_int(\":[x]\");"),
        (":[[x]] = __builtin_annot_intval(\"symb_int\", :[[x]]);", \
                ":[x] = sym_int(\":[x]\");"),
        ('*:[[x]] = __builtin_annot_intval("symb_int", *:[[x]]);', \
                ":[x] = sym_int(\":[x]\");"),
        ('ASSERT(:[assertion]);','assert(:[assertion]);'),
        ('ASSUME(:[assertion]);','assume(:[assertion]);'),
        ('ASSUME (:[assertion]);','assume(:[assertion]);')

]

comby = cby.Comby()
for src in srcs:
    print(f'Transforming {src}...')

    with open(src, 'r') as f:
        data = f.read()

    for p in patterns:
        data = comby.rewrite(data, p[0], p[1])

    with open(src, 'w') as f:
        f.write(data)
