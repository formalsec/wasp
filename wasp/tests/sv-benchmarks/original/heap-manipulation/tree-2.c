extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

#include <stdlib.h>

/* Builds a tree with parent links and
 * checks whether the values are still correct.
 */

extern int __VERIFIER_nondet_int(void);

static void fail(void) {
ERROR: {reach_error();abort();}
}

#define ___MY_ASSERT(cond) do {     \
    if (!(cond))                    \
        fail();                     \
} while (0)

struct node {
    struct node     *left;
    struct node     *right;
    struct node     *parent;
    int             value;
};

static void inspect(struct node *node)
{
    ___MY_ASSERT(node);
    while (node != NULL) {
        if (node->left)
            ___MY_ASSERT(node->left->value == 42);
        ___MY_ASSERT(node->value);
        node = node->parent;
    }
}

struct node *create_tree()
{
    struct node *nodelast = NULL;
    struct node *node = NULL;
    while (__VERIFIER_nondet_int()) {
        node = malloc(sizeof *node);
        if (!node)
            abort();

        node->left = NULL;
        node->right = nodelast;
        if (nodelast)
            nodelast->parent = node;
        int value = __VERIFIER_nondet_int();
        node->value = value;
        nodelast = node;
    }
    while (node != NULL) {
        node->left = malloc(sizeof *node);
        if (!node)
            abort();
        node->left->left = NULL;
        node->left->right = NULL;
        node->left->value = 42;
        node->left->parent = node;
        node = node->right;
    }
    return nodelast;
}

void free_tree(struct node *node) {
    struct node *last = NULL;
    while (1) {
        if (node->right == NULL)
            break;
        node = node->right;
    }
    while (node != NULL) {
        if (node->left)
            free(node->left);
        if (node->right)
            free(node->right);
        last = node;
        node = node->parent;
    }
    free(last);
}

int main()
{
    struct node *data = create_tree();

    if (!data)
        return EXIT_SUCCESS;

    inspect(data);

    free_tree(data);

    return EXIT_SUCCESS;
}
