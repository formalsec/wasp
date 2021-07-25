extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
extern int __VERIFIER_nondet_int();
/*
 * Build NULL-terminated sll of the following form:
 * (N3)*(N4)*(N5)*, s.t. node Ni has a sublist of length i and occurs at most 10 times.
 * Examples: (N3-N3-N3-N4-N5-N5) or (N3-N5-N5-N5).
 * Then check if the sublist lengths are in {3..5} and monotonically increase.
 * Violation of monotonicity assumption: Append a node with a sublist of length 3.
 */
#include <stdlib.h>

typedef struct node {
  struct node* next;
  struct node* inner;
} *SLL;

void myexit(int s) {
 _EXIT: goto _EXIT;
}

SLL sll_create(int len) {
  SLL head = NULL;
  while(len > 0) {
    SLL new_head = (SLL) malloc(sizeof(struct node));
    if(NULL == new_head) {
      myexit(1);
    }
    new_head->next = head;
    head = new_head;
    len--;
  }
  return head;
}

SLL node_create_with_sublist(int sublist_length) {
  SLL new_node = (SLL) malloc(sizeof(struct node));
  if(NULL == new_node) {
    myexit(1);
  }
  new_node->inner = sll_create(sublist_length);
  new_node->next = NULL;
  return new_node;
}

int sll_length(SLL head) {
  int len = 0;
  while(head) {
    len++;
    head = head->next;
  }
  return len;
}

void sll_append(SLL* head, int sublist_length) {
  SLL new_last = node_create_with_sublist(sublist_length);
  new_last->next = NULL;
  SLL temp = *head;
  if(NULL != temp) {
    while(temp->next) {
      temp = temp->next;
    }
    temp->next = new_last;
  } else {
    *head = new_last;
  }
}

void sll_hierarchical_destroy(SLL head) {
 while(head) {
    SLL temp = head->next;
    SLL sub_head = head->inner;
    while(sub_head) {
      SLL temp_2 = sub_head->next;
      free(sub_head);
      sub_head = temp_2;
    }
    free(head);
    head = temp;
  }
}

int main() {
  const int min = 3; /* min. sublist length */
  const int max = 5; /* max. sublist length */
  int i, j;
  SLL head = NULL;
  for(i = min; i <= max; i++) {
    for(j = 0; j < 10 && __VERIFIER_nondet_int(); j++) {
      sll_append(&head, i);
    }
  }
  /* violate monotonicity assumption */
  sll_append(&head, min);
  SLL ptr = head;
  for(i = min; NULL != ptr; i++) {
    if(i > max) {
      goto ERROR;
    }
    while(ptr) {
      int count = sll_length(ptr->inner);
      if(i == count) {
	ptr = ptr->next;
      } else if(3 == i && 5 == count) {
	i++;
	break;
      } else if(i + 1 == count && i < max) {
	break;
      } else { /* reachable! */
	goto ERROR;
      }
    }
  }
  sll_hierarchical_destroy(head);
  return 0;
 ERROR: {reach_error();abort();}
  return 1;
}
