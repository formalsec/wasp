#define __VERIFIER_assert(cond) do { if (!(cond)) {reach_error();abort();}} while (0)
/**
 * Red-black list, i.e. a list with coloured nodes (black or red) that satisfies
 * the condition B . (B + RB)*
 */

#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

typedef enum {RED, BLACK} Colour;

typedef struct TSLL
{
	struct TSLL* next;
	struct TSLL* prev;
	Colour colour;
} SLL;

int main()
{
	// create the head
	SLL* list = malloc(sizeof(SLL));
	list->next = NULL;
	list->prev = NULL;
	list->colour = BLACK;

	SLL* end = list;

	// create an arbitrarily long tail
	while (__VERIFIER_nondet_int())
	{
		// create a node
		end->next = malloc(sizeof(SLL));
		end->next->prev = end;
		end = end->next;
		end->next = NULL;

		if (__VERIFIER_nondet_int())
		{	// mark the node as black
			end->colour = BLACK;
		}
		else
		{	// mark the node as red and follow it by a black node
			end->colour = RED;
			end->next = malloc(sizeof(SLL));
			end->next->prev = end;
			end = end->next;
			end->next = NULL;
			end->colour = BLACK;
		}
	}

	end = NULL;
	end = list;

	// check the invariant
	__VERIFIER_assert(NULL != end);
	__VERIFIER_assert(BLACK == end->colour);

	while (NULL != end)
	{
		if (RED == end->colour)
		{
			end = end->next;
			end = end->next;
		}

		__VERIFIER_assert(end->next);
		end = end->next;
	}

	// destroy the list
	while (NULL != list)
	{
		if (RED == list->colour)
		{	// we can remove two nodes at once
			end = list->next;
			free(list);
			list = end->next;
			free(end);
		}
		else
		{	// we can remove only one node
			end = list->next;
			free(list);
			list = end;
		}
	}

	return 0;
}
