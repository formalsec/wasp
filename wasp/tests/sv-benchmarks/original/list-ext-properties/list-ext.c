extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

extern int __VERIFIER_nondet_int();
/*
 * Simple example: build a list with only 1s, then 2s and finally
 * on 3 (arbitrary length); afterwards, go through it and check
 * if the the list does have the correct form, and in particular
 * finishes by a 3.
 */
#include <stdlib.h>

void myexit(int s) {
  _EXIT: goto _EXIT;
}

typedef struct node {
  int h;
  struct node *n;
} *List;

int main() {

  int i = 0;
  int y = 0;

  /* Build a list of the form 1->...->1->2->....->2->3 */
  List a = (List) malloc(sizeof(struct node));

  if (a == 0) myexit(1);

  List t;
  List p = a;
  while (i < 10 && __VERIFIER_nondet_int()) {
    i++;
    p->h = 1;
    t = (List) malloc(sizeof(struct node));

    if (t == 0) myexit(1);

    p->n = t;
    p = p->n;
  }
  while (y < 10 && __VERIFIER_nondet_int()) {
    y++;
    p->h = 2;
    t = (List) malloc(sizeof(struct node));

    if (t == 0) myexit(1);

    p->n = t;
    p = p->n;
  }
  p->h = 3;
  p->n = 0;
  
  i = 0;
  y = 0;
    
  /* Check it */
  p = a;
  while (p->h == 1) {
    i++;
    p = p->n;
  }
  while (p->h == 2) {
    y++;
    p = p->n;
  }

  if(p->h != 3 || (i + y) < 20)
    ERROR: {reach_error();abort();}

  /* free memory */
  p = a;
  while (p->n != 0) {
    t = p->n;
    free(p);
    p = t;
  }
  free(p);

  return 0;
}
