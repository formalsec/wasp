extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();
void *malloc(unsigned int size);
#define SIZE 1000000
#define NULL 0
struct S
{
	int n;
	int *p;
};
struct S *a[SIZE];

int main()
{

	int i;

	for (i = 0; i < SIZE; i++)
	{
		struct S *s1 = (struct S *) malloc(sizeof(struct S));
		s1->n = __VERIFIER_nondet_int();

		if (s1->n == 0)
		{
			s1->p = (int *) malloc(sizeof(int));
		}
		else
		{
			s1->p = NULL;
		}

		a[i] = s1;
	}

	for (i = 0; i < SIZE; i++)
	{
		struct S *s2 = a[i];
		if (s2->n == 0)
		{
			__VERIFIER_assert(s2->p != NULL);
		}
	}

	return 0;
}
