#include "list.h"
#include "utils.h"
#include "mockups.h" 

static List *list1;
static List *list2;

int a, b, c, d, e, f, g, h;

void setup_tests() {
    list_new(&list1), list_new(&list2);

    a = dyn_sym_int32('a');
    b = dyn_sym_int32('b');
    c = dyn_sym_int32('c');
    d = dyn_sym_int32('d');
    e = dyn_sym_int32('e');
    f = dyn_sym_int32('f');
    g = dyn_sym_int32('g');
    h = dyn_sym_int32('h');

    int *va = (int *)malloc(sizeof(int));
    int *vb = (int *)malloc(sizeof(int));
    int *vc = (int *)malloc(sizeof(int));
    int *vd = (int *)malloc(sizeof(int));

    *va = a;
    *vb = b;
    *vc = c;
    *vd = d;

    list_add(list1, va);
    list_add(list1, vb);
    list_add(list1, vc);
    list_add(list1, vd);

    va = (int *)malloc(sizeof(int));
    vb = (int *)malloc(sizeof(int));
    vc = (int *)malloc(sizeof(int));
    vd = (int *)malloc(sizeof(int));

    *va = e;
    *vb = f;
    *vc = g;
    *vd = h;

    list_add(list2, va);
    list_add(list2, vb);
    list_add(list2, vc);
    list_add(list2, vd);
}

void teardown_test() {
    list_destroy_cb(list1, free);
    list_destroy(list2);
}

int main() {
    setup_tests();

    List *cp;
    list_copy_deep(list1, copy, &cp);
    assert(4 == list_size(cp));

    int *e;
    list_get_at(cp, 2, (void *)&e);

    int *le;
    list_get_at(list1, 2, (void *)&le);
    assert(*e == *le);

    list_get_at(cp, 2, (void *)&e);
    list_get_at(list1, 2, (void *)&le);
    assert(e != le);

    list_destroy_cb(cp, free);

    teardown_test();
}
