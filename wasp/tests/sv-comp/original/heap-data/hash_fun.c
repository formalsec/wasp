extern int __VERIFIER_nondet_int();
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

#include <stdlib.h>

#define INTERVAL_SIZE 100

struct node {
    int hash;
    struct node *next;
};

int hash_fun() { return __VERIFIER_nondet_int(); }

void append_to_list(struct node **list, int hash) {
    struct node *node = malloc(sizeof(*node));
    node->next = *list;
    node->hash = hash;
    *list = node;
}

int main() {
    struct node *list = NULL;

    int base = __VERIFIER_nondet_int();

    while (__VERIFIER_nondet_int()) {
        if (base >= 0 && base <= 1000000) {
            base = base + 0;
            int hash = hash_fun();

            if (hash > base && hash < base + INTERVAL_SIZE)
                append_to_list(&list, hash);
        }
    }

    while (list) {
        if (!(list->hash >= base && list->hash < base + INTERVAL_SIZE))
            {reach_error();}
        list = list->next;
    }
}
