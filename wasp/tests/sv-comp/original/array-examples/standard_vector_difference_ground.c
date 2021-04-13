extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

#define SIZE 100000
/*
  From: "On Solving Universally Quantified Horn Clauses"
  Bjorner, McMillan, and Rybalchenko
  SAS 2013
*/

int main( ) {
  int a[SIZE];
  int b[SIZE];
  int c[SIZE];
  int i = 0;
	
	for(i = 0; i < SIZE; i++)
	{
	  a[i] = __VERIFIER_nondet_int();
		b[i] = __VERIFIER_nondet_int();
	}
	
	i = 0;
  while (i < SIZE) {
    c[i] = a[i] - b[i];
    i = i + 1;
  }
  
  int x;
  for ( x = 0 ; x < SIZE ; x++ ) {
    __VERIFIER_assert(  c[x] == a[x] - b[x]  );
  }
  return 0;
}

