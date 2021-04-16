extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

extern int __VERIFIER_nondet_int();
/*
 * Alternating list example: 
 * creats a list with 1s at odd positions and 2s at even ones. 
 * Then, it goes through and checks if the alternation holds.
 */
#include <stdlib.h>

typedef struct node {
  int h;
  struct node *n;
} *List;

void myexit(int s) {
	_EXIT: goto _EXIT;
}

int main() {
  int flag = 1;
  
  /* Build a list of the form (1->2)*->0 */
  List a = (List) malloc(sizeof(struct node));
  if (a == 0) myexit(1);
  List t;
  List p = a;
  while (__VERIFIER_nondet_int()) {
    if (flag) {
      p->h = 1;
      flag = 0;
    } else {
      p->h = 2;
      flag = 1;
    }
    t = (List) malloc(sizeof(struct node));
    if (t == 0) myexit(1);
    p->n = t;
    p = p->n;
  }
  p->h = 3;

  /* Check it */
  p = a;
  flag = 1;
  while (p->h != 3) {
    if (flag) {
      flag = 0;
      if (p->h != 1)
	goto ERROR;
    } else {
      flag = 1;
      if (p->h != 2)
	goto ERROR;
    }
    p = p->n;
  }

  /* Destroy the list */
  p = a;
  while (p->h != 3) {
    List tmp = p;
    p = p->n;
    free(tmp);
  }
  free(p);

  return 0;

  ERROR: {reach_error();abort();}
    return 1;
}
