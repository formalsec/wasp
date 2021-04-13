extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

#define N 100000

int main ( ) {
  int A[ N ];
  int B[ N ];
  int C[ N ]; 
  int i;
  int j = 0;
	
  for (i = 0; i < N ; i++) {
    A[i] = __VERIFIER_nondet_int();
    B[i] = __VERIFIER_nondet_int();
  }	
	
	for (i = 0; i < N ; i++) {
    if ( A[i] == B[i] ) {
      C[j] = i;
      j = j + 1;
    }
  }

  
  int x; 
  for ( x = 0 ; x < j ; x++ ) {
    __VERIFIER_assert(  C[x] <= x + i - j  );
  }
  for ( x = 0 ; x < j ; x++ ) {
    __VERIFIER_assert(  C[x] >= x  );
  }
  return 0;
}
