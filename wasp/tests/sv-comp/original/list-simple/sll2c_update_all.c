extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
/*
 * Create circular sll of size 2: 1-1
 * Update all nodes in a forward traversal. Check result: 2-3
 */
#include <stdlib.h>

typedef struct node {
  struct node *next;
  int data;
} *SLL;

void myexit(int s) {
 _EXIT: goto _EXIT;
}

SLL node_create(int data) {
  SLL temp = (SLL) malloc(sizeof(struct node));
  if(NULL == temp) {
    myexit(1);
  }
  temp->next = NULL;
  temp->data = data;
  return temp;
}

SLL sll_circular_create(int len, int data) {
  SLL head = node_create(data);
  SLL last = head;
  while(len > 1) {
    SLL new_head = node_create(data);
    new_head->next = head;
    head = new_head;
    len--;
  }
  last->next = head;
  return head;
}

void sll_circular_destroy(SLL head) {
  if(NULL != head) {
    SLL p = head->next;
    while(p != head) {
      SLL q = p->next;
      free(p);
      p = q;
    }
    free(head);
  }
}

int sll_circular_get_data_at(SLL head, int index) {
  while(index > 0) {
    head = head->next;
    index--;
  }
  return head->data;
}

void sll_circular_update_at(SLL head, int data, int index) {
  while(index > 0) {
    head = head->next;
    index--;
  }
  head->data = data;
}

int main() {
  const int len = 2;
  const int data = 1;
  SLL s = sll_circular_create(len, data);
  int i = 0;
    for(i = 0; i < len; i++) {
    int new_data = i + len;
    sll_circular_update_at(s, new_data, i);
  }
  for(i = 0; i < len; i++) {
    int expected = i + len;
    if(expected != sll_circular_get_data_at(s, i)) {
      goto ERROR;
    }
  }
  sll_circular_destroy(s);
  return 0;
 ERROR: {reach_error();abort();}
  return 1;
}
