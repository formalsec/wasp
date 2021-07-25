extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

#define N 100000

int main( ) {
  int src[N];
  int dst[N];
  int i = 0; 
	
	for (i = 0; i < N; i++)
	{
	    src[i] = __VERIFIER_nondet_int();
	}
	
	i = 0;
	
  while ( src[i] != 0 ) {
    dst[i] = src[i];
    i = i + 1;
  }
  
  int x;
  for ( x = 0 ; x < i ; x++ ) {
    __VERIFIER_assert(  dst[x] == src[x]  );
  }
  return 0;
}

