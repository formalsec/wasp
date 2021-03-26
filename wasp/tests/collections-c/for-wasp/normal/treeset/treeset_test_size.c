#include "treeset.h"
#include "utils.h"
#include "mockups.h" 

static TreeSet *set;

int main() {
    treeset_new(cmp, &set);

    int a = dyn_sym_int32('a');
    int b = dyn_sym_int32('b');
    int c = dyn_sym_int32('c');
    assume(a != b && a != c && b != c);

    treeset_add(set, &a);
    treeset_add(set, &b);
    treeset_add(set, &c);

    assert(3 == treeset_size(set));
}
