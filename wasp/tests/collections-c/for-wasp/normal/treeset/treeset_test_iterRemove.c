#include "treeset.h"
#include "utils.h"
#include "mockups.h" 

static TreeSet *set;

int main() {
    treeset_new(cmp, &set);

    int a = sym_int("a", 32);
    int b = sym_int("b", 32);
    int c = sym_int("c", 32);
    assume(a != b && a != c && b != c);

    treeset_add(set, &a);
    treeset_add(set, &b);
    treeset_add(set, &c);

    TreeSetIter iter;
    treeset_iter_init(&iter, set);

    void *e;
    while (treeset_iter_next(&iter, &e) != CC_ITER_END) {
        if (*((int *)e) == b)
            treeset_iter_remove(&iter, NULL);
    }
    assert(2 == treeset_size(set));
    assert(0 == treeset_contains(set, &b));
}
