extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "arctan_Pade.c", 3, "reach_error"); }
/* Example from "Towards an industrial use of FLUCTUAT on safety-critical 
   avionics software" by Delmas, Goubault, Putot, Souryis, Tekkal,
   and Védrine. Published in FMICS 09.

   Padé approximation of arctan.
*/


extern double __VERIFIER_nondet_double();
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error();abort();} } return; }


const double Pi=3.141592653589793238;

double PADE_2_2(double x) 
{
  double x_2 = x*x;
  return 1. - x_2 / (3. + 9./5.*x_2);
}

double ARCTAN_0_1(double x)
{
  return x*PADE_2_2(x);
}

double ARCTAN_POS(double x)
{
  if (x > 1.) return Pi / 2. - ARCTAN_0_1(1. / x);
  else return ARCTAN_0_1(x);
}

double ARCTAN(double x)
{
  if (x < 0) return -ARCTAN_POS(-x);
  else return ARCTAN_POS(x);
}

int main()
{
  double a, r;

  a = __VERIFIER_nondet_double();
  assume_abort_if_not(a >= -1.79e308 && a <= 1.79e308);

  r = ARCTAN(a);
  
  __VERIFIER_assert(r >= -1.571 && r <= 1.571);
  return 0;
}
