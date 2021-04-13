extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "pr2.c", 3, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int(void);

int CELLCOUNT;

int main()
{
	CELLCOUNT = __VERIFIER_nondet_int();
	if(CELLCOUNT > 1)
	{
		int MINVAL;
		int i;
		int volArray[CELLCOUNT];
		int CCCELVOL2 = 3;
		int CCCELVOL1 = 1;

		if(CELLCOUNT % 2 != 0) { return 1; }

		assume_abort_if_not(CELLCOUNT % 2 == 0);
		for(i = 1; i <= CELLCOUNT/2; i++)
		{
			if(CCCELVOL2 >= MINVAL)
			{
				volArray[i*2 - 2] = CCCELVOL2;
			}
			else
			{
				volArray[i*2 - 2] = 0;
			}

			if(CCCELVOL1 >= MINVAL)
			{
				volArray[i*2 - 1] = CCCELVOL1;
			}
			else
			{
				volArray[i*2 - 1] = 0;
			}
		}

		for(i = 0; i < CELLCOUNT; i++)
		{
			__VERIFIER_assert(volArray[i] >= MINVAL || volArray[i] == 0 );
		}
	}
	return 1;
}
