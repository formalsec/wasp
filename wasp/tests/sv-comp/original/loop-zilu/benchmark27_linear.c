#include <assert.h>
void reach_error(void) {assert(0);}

extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}

/* 27.cfg:
names=i j k
precondition=i<j && k>i-j
loopcondition=i<j
loop=k=k+1; i=i+1;
postcondition=k > 0
learners=linear
*/
int main() {
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  if (!(i<j && k>i-j)) return 0;
  while (i<j) {
    k=k+1;
    i=i+1;
  }
  __VERIFIER_assert(k > 0);
  return 0;
}
