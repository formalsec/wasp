extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "water_pid.c", 3, "reach_error"); }
/* Example from "Some future challenges in the validation of control
   systems" by Goubault, Martel, and Putot, published at ERTS 06
*/

void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error();abort();} } return; }


typedef double NUM;
static NUM yn = 0;

NUM ui = 0;

NUM y(int i) 
{
  yn += ui;
  return yn;
}

int main() 
{
  NUM yi, yc;
  NUM K;
  NUM T;
  NUM taui;
  NUM taud;
  NUM ei, sumej, epi;
  int i;
  T = 1;
  taui = 1;
  taud = 1;
  K = .5;
  yc = .5;
  yi = y(0);
  epi = yc-yi;
  sumej = epi;
  for (i=0; i<120; i++) {
    yi = y(i);
    ei = yc-yi;
    sumej = sumej+ei;
    ui = K*(ei+sumej*T/taui+taud/T*(ei-epi));
    epi = ei;

    __VERIFIER_assert(epi >= -1. && epi <= 1.);
  }
  return 0;
}
