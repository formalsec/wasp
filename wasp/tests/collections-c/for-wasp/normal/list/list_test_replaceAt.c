#include "list.h"
#include "mockups.h" 

static List *list1;
static List *list2;

int a, b, c, d, e, f, g, h;

void setup_tests() {
    list_new(&list1), list_new(&list2);

    a = sym_int("a", 32);
    b = sym_int("b", 32);
    c = sym_int("c", 32);
    d = sym_int("d", 32);
    e = sym_int("e", 32);
    f = sym_int("f", 32);
    g = sym_int("g", 32);
    h = sym_int("h", 32);

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

    int *rr = (int *)malloc(sizeof(int));
    int r = sym_int("r", 32);

    *rr = r;

    int *r_ptr;
    list_replace_at(list1, rr, 2, (void *)&r_ptr);
    free(rr);

    list_get_at(list1, 2, (void *)&r_ptr);
    assert((int *)r_ptr == rr);

    teardown_test();
}
