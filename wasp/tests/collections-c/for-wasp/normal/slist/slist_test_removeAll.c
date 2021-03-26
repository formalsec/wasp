#include "slist.h"
#include "mockups.h" 

static SList *list;
static SList *list2;
static int stat;

int a, b, c, d, e, f, g, h;

void setup_test() {
    slist_new(&list), slist_new(&list2);

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

    slist_add(list, va);
    slist_add(list, vb);
    slist_add(list, vc);
    slist_add(list, vd);

    va = (int *)malloc(sizeof(int));
    vb = (int *)malloc(sizeof(int));
    vc = (int *)malloc(sizeof(int));
    vd = (int *)malloc(sizeof(int));

    *va = e;
    *vb = f;
    *vc = g;
    *vd = h;

    slist_add(list2, va);
    slist_add(list2, vb);
    slist_add(list2, vc);
    slist_add(list2, vd);
};

void teardown_test() {
    slist_destroy(list);
    slist_destroy(list2);
};

int main() {
    setup_test();

    slist_remove_all_cb(list, free);
    assert(0 == slist_size(list));

    void *e = NULL;
    slist_get_first(list, &e);
    assert(e == NULL);

    teardown_test();
    return 0;
}
