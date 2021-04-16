#include <assert.h>
void reach_error(void) {assert(0);}

extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}

/* 22.cfg:
names= x y
precondition=x==1 && y==0
loopcondition=
loop=x=x+y; y++;
postcondition=x >= y
learners=conj
*/
int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (!(x==1 && y==0)) return 0;
  while (__VERIFIER_nondet_bool()) {
    x=x+y;
    y++;
  }
  __VERIFIER_assert(x >= y);
  return 0;
}
