


extern void abort(void);

extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "xor4.c", 6, __extension__ __PRETTY_FUNCTION__); })); }
extern int __VERIFIER_nondet_int();

int xor (int x[100000])
{
  int i;
  long long res;
  res = x[0];
  for (i = 1; i < 100000; i++) {
    res = res ^ x[i];
  }
  return res;
}

int main ()
{
  int x[100000];
  int temp;
  int ret;
  int ret2;
  int ret5;

  for (int i = 0; i < 100000; i++) {
    x[i] = __VERIFIER_nondet_int();
  }

  ret = xor(x);

  temp=x[0];x[0] = x[1]; x[1] = temp;
  ret2 = xor(x);
  temp=x[0];
  for(int i =0 ; i<100000 -1; i++){
     x[i] = x[i+1];
  }
  x[100000 -1] = temp;
  ret5 = xor(x);

  if(ret != ret2 || ret !=ret5){
    {reach_error();}
  }
  return 1;
}
