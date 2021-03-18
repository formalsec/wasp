#include "mockups.h"

long f(long x) {
  if (x % 2 == 0)
    return x / 2;
  else if (x % 3 == 0)
    return x / 3;
  else
    return 3 * x + 1;
}


int logic_bomb(char *s) {
  int symvar = s[0] - 48;
  symvar = symvar + 94;
  long j = f(symvar);
  int loopcount = 1;
  while (j != 1) {
    j = f(j);
    ++loopcount;
  }
  if (loopcount == 25)
    return 3;
  else 
    return 0;
}

void init_symbolic_string(char *s, int sz)
{
  int i;

  for (i = 0; i < sz; ++i) {
    s[i] = dyn_sym_int32(i + '0');
    assume(s[i] > 0);
    assume(s[i] < 127);
  }

  s[i] = '\00';
}

int main() {
  char s[5];
  init_symbolic_string(s, 4);
  int ret = logic_bomb(s);
  assert (ret == 3);
}
