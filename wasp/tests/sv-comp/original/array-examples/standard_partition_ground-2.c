extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

#define N 100000

int main( ) {
  int aa[N];
  int a = 0;
  int b = 0;
  int c = 0;
  int bb[N];
  int cc[N];
	
	for(int i = 0 ; i < N ; i++ ) {
    aa[i] = __VERIFIER_nondet_int();
  }
  
  while( a < N ) {
    if( aa[ a ] >= 0 ) {
      bb[ b ] = aa[ a ];
      b = b + 1;
    }
    a = a + 1;
  }
  a = 0;
  while( a < N ) {
    if( aa[ a ] < 0 ) {
      cc[ c ] = aa[ a ];
      c = c + 1;
    }
    a = a + 1;
  }

  int x;
  for ( x = 0 ; x < b ; x++ ) {
    __VERIFIER_assert(  bb[ x ] >= 0  );
  }
  return 0;
}


