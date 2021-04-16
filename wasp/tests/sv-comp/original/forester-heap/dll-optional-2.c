#define __VERIFIER_assert(cond) do { if (!(cond)) {reach_error();abort();}} while (0)
/*
 * A list with nodes which can point to an optional
 * external node. Whether an optional node is allocated
 * or not is determined by integer value -- the value 2
 * determines allocated external node, 1 or 0 means no
 * external node.
 *
 * Part of Forester benchmark
 */

#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

#define ALLOC_DATA(X) \
	if (__VERIFIER_nondet_int()) \
	{ \
		X->data = 2; \
		X->opt = malloc(sizeof(SLL)); \
		X->opt->next = NULL; \
	} \
	else if (__VERIFIER_nondet_int()) \
	{ \
		X->data = 1; \
		X->opt = X; \
	} \
	else \
	{ \
		X->data = 0; \
		X->opt = X; \
	}

#define ALLOC_NODE(X) \
	X->next = malloc(sizeof(SLL)); \
	X->next->prev = X; \
	X = X->next; \
	X->next = NULL; \
	ALLOC_DATA(X)

#define ALLOC_NONDET(X)          \
	while (__VERIFIER_nondet_int()) \
	{ \
		ALLOC_NODE(X) \
	}

typedef struct TSLL
{
	struct TSLL* next;
	struct TSLL* prev;
	struct TSLL* opt;
	int data;
} SLL;

int main()
{
	// create the head
	SLL* head = malloc(sizeof(SLL));
	head->next = NULL;
	head->prev = NULL;
	ALLOC_DATA(head)
	SLL* x = head;

	ALLOC_NONDET(x)

	// check the invariat
	x = head;
	while (x != NULL)
	{
		__VERIFIER_assert(x->data == 2 && x->opt == x);
		x = x->next;
	}

	x = head;
	// destroy the list
	while (x != NULL)
	{
		head = x;
		x = x->next;
		if (head->data == 2)
			free(head->opt);
		free(head);
	}

	return 0;
}
