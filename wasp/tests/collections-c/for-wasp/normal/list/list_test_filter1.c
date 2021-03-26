#include "list.h"
#include "mockups.h" 

static List *list1;
static List *list2;

bool pred1(const void *e) { return *(int *)e == 0; }

bool pred2(const void *e) { return *(int *)e > 3; }

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

    assume(a != 0 && b != 0 && c != 0 && d != 0);

    List *filter = NULL;
    list_filter(list1, pred1, &filter);

    assert(4 == list_size(list1));
    assert(0 == list_size(filter));

    void *e = NULL;
    list_get_first(filter, &e);
    assert(e == NULL);

    list_get_last(filter, &e);
    assert(e == NULL);
    free(filter);

    teardown_test();
}
