extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
extern int __VERIFIER_nondet_int(void);

/*
 * Simple example: build a list with only 1s and finally a 0 (arbitrary length); 
 * afterwards, go through it and check if the list does have the correct form, and in particular
 * finishes by a 0.
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
  /* Build a list of the form 0->1->...->29->30 */
  List a = (List) malloc(sizeof(struct node));

  if (a == 0) myexit(1);

  List t;
  List p = a;
  
  int i = 0;
  
  while (i < 30 && __VERIFIER_nondet_int()) {  
    p->h = i;
    t = (List) malloc(sizeof(struct node));

    if (t == 0) myexit(1);

    p->n = t;
    p = p->n;
    i++;
  }
  
  p->h = i;
  p->n = 0;
  p = a;
  i = 0;
  while (p!=0) {
    if (p->h != 1) {
      ERROR: {reach_error();abort();}
    }
    p = p->n;
    i++;
  }

  p = a;
  while (p!=0) {
    struct node *tmp = p->n;
    free(p);
    p = tmp;
  }

  return 0;
}
