#include <assert.h>
void reach_error(void) {assert(0);}

extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}

/* 38.cfg:
names=x y
beforeloop=
precondition=x == y && y == 0 
loopcondition=
loop=x+=4;y++;
postcondition=x == 4*y && x >= 0
learners= conj
*/
int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (!(x == y && y == 0)) return 0;
  while (__VERIFIER_nondet_bool()) {
    x+=4;y++;
  }
  __VERIFIER_assert(x == 4*y && x >= 0);
  return 0;
}
