#include "stack.h"
#include "mockups.h" 

static Stack *s;

void setup_tests() { stack_new(&s); }

void teardown_tests() { stack_destroy(s); }

int main() {
    setup_tests();

    int a = dyn_sym_int32('a');
    int b = dyn_sym_int32('b');
    int c = dyn_sym_int32('c');

    int *p;

    stack_push(s, (void *)&a);
    stack_peek(s, (void *)&p);
    assert(&a == p);

    stack_push(s, (void *)&b);
    stack_peek(s, (void *)&p);
    assert(&b == p);

    stack_push(s, (void *)&c);
    stack_peek(s, (void *)&p);
    assert(&c == p);

    teardown_tests();
    return 0;
}
