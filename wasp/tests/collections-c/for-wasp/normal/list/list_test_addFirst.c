#include "list.h"
#include "mockups.h" 

static List *list1;
static List *list2;

void setup_tests() { list_new(&list1), list_new(&list2); }

void teardown_test() {
    list_destroy(list1);
    list_destroy(list2);
}

int main() {
    setup_tests();

    int a = dyn_sym_int32('a');
    int b = dyn_sym_int32('b');
    int c = dyn_sym_int32('c');
    int d = dyn_sym_int32('d');
    int p = dyn_sym_int32('p');

    list_add(list1, &a);
    list_add(list1, &b);
    list_add(list1, &c);
    list_add(list1, &d);

    assert(4 == list_size(list1));

    int *first;
    list_get_first(list1, (void *)&first);
    assert(a == *first);

    list_add_last(list1, &p);
    assert(5 == list_size(list1));

    list_get_last(list1, (void *)&first);
    assert(p == *first);

    teardown_test();
}
