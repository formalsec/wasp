/*
 * Benchmarks used in the paper "Commutativity of Reducers" 
 * which was published at TACAS 2015 and 
 * written by Yu-Fang Chen, Chih-Duo Hong, Nishant Sinha, and Bow-Yaw Wang.
 * http://link.springer.com/chapter/10.1007%2F978-3-662-46681-0_9
 * 
 * We checks if a function is "deterministic" w.r.t. all possible permutations 
 * of an input array.  Such property is desirable for reducers in the 
 * map-reduce programming model.  It ensures that the program always computes 
 * the same results on the same input data set.
 */

#define N 5
#define fun rangesum

extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
extern int __VERIFIER_nondet_int();

void init_nondet(int x[N]) {
  int i;
  for (i = 0; i < N; i++) {
    x[i] = __VERIFIER_nondet_int();
  }
}

int rangesum (int x[N])
{
  int i;
  long long ret;
  ret = 0;
  int cnt = 0;
  for (i = 0; i < N; i++) {
    if( i > N/2){
       ret = ret + x[i];
       cnt = cnt + 1;
    }
  }
  if ( cnt !=0)
    return ret / cnt;
  else
    return 0;
}

int main ()
{
  int x[N];
  init_nondet(x);
  int temp;
  int ret;
  int ret2;
  int ret5;

  ret = fun(x);

  temp=x[0];x[0] = x[1]; x[1] = temp;
  ret2 = fun(x);
  temp=x[0];
  for(int i =0 ; i<N-1; i++){
     x[i] = x[i+1];
  }
  x[N-1] = temp;
  ret5 = fun(x);

  if(ret != ret2 || ret !=ret5){ 
    {reach_error();}
  }
  return 1;
}
