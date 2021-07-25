extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

#define N 100000
int main( ) {
  int src[N];
  int dst[N];
  int i = 0; 
  int j = 0;

  while ( j < N ) {
    src[j] = __VERIFIER_nondet_int();
    j = j + 1;
  }

  while ( i < N && src[i] != 0 ) {
    dst[i] = src[i];
    i = i + 1;
  }
  
  i = 0;
  while ( i < N && src[i] != 0 ) {
    __VERIFIER_assert(  dst[i] == src[i]  );
    i = i + 1;
  }
  return 0;
}

