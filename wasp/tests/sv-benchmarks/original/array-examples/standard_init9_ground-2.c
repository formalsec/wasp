extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

#define N 100000

int main ( ) {
  int a[N];
  int i = 0;
  while ( i < N ) {
    a[i] = 42;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 43;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 44;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 45;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 46;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 47;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 48;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 49;
    i = i + 1;
  }
  i = 0;
  while ( i < N ) {
    a[i] = 50;
    i = i + 1;
  }

  int x;
  for ( x = 0 ; x < N ; x++ ) {
    __VERIFIER_assert(  a[x] == 50  );
  }
  return 0;
}
