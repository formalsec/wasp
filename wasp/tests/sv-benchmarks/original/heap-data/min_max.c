extern int __VERIFIER_nondet_int();
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

#include <stdlib.h>
#include <limits.h>

#define APPEND(l,i) {i->next=l; l=i;}

typedef struct node {
    struct node *next;
    int val;
} Node;

int main() {
    Node *l = NULL;
    int min = INT_MAX, max = -INT_MAX;
 
    while (__VERIFIER_nondet_int()) {
        Node *p = malloc(sizeof(*p));
        p->val = __VERIFIER_nondet_int();
        APPEND(l, p)
        
        if (min > p->val) {
            min = p->val;
        }
        if (max < p->val) {
            max = p->val;
        }

    }

    Node *i = l;
    while (i != NULL) {
        if (i->val < min)
            {reach_error();}
        if (i->val > max)
            {reach_error();}
        i = i->next;
    }
}
