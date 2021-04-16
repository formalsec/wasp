#define __VERIFIER_assert(cond) do { if (!(cond)) {reach_error();abort();}} while (0)
/*
 * We create a list with nodes containing the integers 0, 1, 2, and 3.
 * The list can form sequences 0, 01, 012, 0123^*. A particular sequence is created
 * during construction of the list nondeterministically. We remember which sequence was actually created
 * by an auxiliary integer variable. Then we traverse the list and check that
 * the sequence formed by the list corresponds to the value of the auxiliary variable.
 *
 * Part of Forester benchmark
 */

#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

typedef struct TSLL
{
	struct TSLL* next;
	struct TSLL* prev;
	int data;
} SLL;

int main()
{
	// create the head
	SLL* head = malloc(sizeof(SLL));
	head->next = NULL;
	head->prev = NULL;
	head->data = 0;
	SLL* item = head;
	int status = 0;
	
	while (__VERIFIER_nondet_int())
	{
		item->next = malloc(sizeof(SLL));
		item->next->prev = item;
		item = item->next;
		item->next = NULL;

		if (!status)
		{
			item->data = 1;
			status = 1;
		}
		else if (status == 1)
		{
			item->data = 2;
			status = 2;
		}
		else if (status >= 2)
		{
			item->data = 3;
			status = 3;
		}

		__VERIFIER_assert(head != NULL);
		__VERIFIER_assert(item != NULL);
	}

	__VERIFIER_assert(head != NULL);
	if (status == 1)
	{
		__VERIFIER_assert(head != NULL);
		__VERIFIER_assert(head->next != NULL);
	}
	if (status == 2)
	{
		__VERIFIER_assert(head != NULL);
		__VERIFIER_assert(head->next != NULL);
		__VERIFIER_assert(head->next->next != NULL);
	}
	if (status == 3)
	{
		__VERIFIER_assert(head != NULL);
		__VERIFIER_assert(head->next != NULL);
		__VERIFIER_assert(head->next->next != NULL);
		__VERIFIER_assert(head->next->next->next != NULL);
		__VERIFIER_assert(head->next->next->next->data != 3);
	}

	item = head->next;
	while(item && __VERIFIER_nondet_int())
	{
		__VERIFIER_assert(!status || item->data > 0);
		item = item->next;
	}


	while(head)
	{
		item = head;
		head = head->next;
		free(item);
	}

	return 0;
}
