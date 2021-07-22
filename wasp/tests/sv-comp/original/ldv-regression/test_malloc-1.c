extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
#include <assert.h>
#include <stdlib.h>

//#ifdef BLAST_AUTO_1
/* using malloc */

int CURRENTLY_UNSAFE;
//#else
/* using separate variables */
/*

int CURRENTLY_UNSAFE;
#endif
*/

int main(void) {
//#ifdef BLAST_AUTO_1
	int * p1 = malloc(sizeof(int));
	int * p2 = malloc(sizeof(int));
/*
#else
	int a,b;
	int *p1=&a;
	int *p2=&b;
#endif
*/
	if(p1!=0 && p2!=0) {
		__VERIFIER_assert(p1!=p2);
	}
	return 0;
}
