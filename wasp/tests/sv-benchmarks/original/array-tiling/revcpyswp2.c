//array-reversecopynswap-twice
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "revcpyswp2.c", 4, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int(void);
void *malloc(unsigned int size);

int SIZE;

const int MAX = 100000;

int main()
{
	SIZE = __VERIFIER_nondet_int();
	if(SIZE > 1 && SIZE < MAX)
	{
		int i;
		int tmp;
		int *a = malloc(sizeof(int)*SIZE);
		int *b = malloc(sizeof(int)*SIZE);
		int *a_copy = malloc(sizeof(int)*SIZE);
		int *b_copy = malloc(sizeof(int)*SIZE);
		
		for(i=0; i<SIZE; i++)
		{
			a_copy[i] = __VERIFIER_nondet_int();
			b_copy[i] = __VERIFIER_nondet_int();
		}
		
		//reverse copy
		for(i=0; i<SIZE; i++)
		{
			a[i] = a_copy[SIZE-i-1];
			b[i] = b_copy[SIZE-i-1];
		}

		//swap
		for(i=0; i<SIZE; i++)
		{
			tmp = a[i];
			a[i] = b[i];
			b[i] = tmp;
		}

		//swap
		for(i=0; i<SIZE; i++)
		{
			tmp = a[i];
			a[i] = b[i];
			b[i] = tmp;
		}

		//assert
		for(i=0; i<SIZE; i++)
		{
			__VERIFIER_assert(a[i] == a_copy[SIZE-i-1]);
			//__VERIFIER_assert(b[i] == b_copy[SIZE-i-1]);
		}
	}
	return 1;
}
