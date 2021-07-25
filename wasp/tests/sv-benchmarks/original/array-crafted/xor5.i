

extern void abort(void);

extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "xor5.c", 5, __extension__ __PRETTY_FUNCTION__); })); }
extern int __VERIFIER_nondet_int(void);

int N;

int xor (int x[N])
{
  int i;
  long long res;
  res = x[0];
  for (i = 1; i < N; i++) {
    res = res ^ x[i];
  }
  return res;
}

int main ()
{
  N = __VERIFIER_nondet_int();
  if (N > 1) {
    int x[N];
    int temp;
    int ret;
    int ret2;
    int ret5;
		
		for(int i = 0; i < N; i++) 
		{
		  x[i] = __VERIFIER_nondet_int();
		}

    ret = xor(x);

    temp=x[0];x[0] = x[1]; x[1] = temp;
    ret2 = xor(x);
    temp=x[0];
    for(int i =0 ; i<N-1; i++){
       x[i] = x[i+1];
    }
    x[N-1] = temp;
    ret5 = xor(x);

    if(ret != ret2 || ret !=ret5){
      {reach_error();}
    }
  }
  return 1;
}
