extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
/*
 * DLL circular example:
 * Build circular dll (1-1-1-1-1).
 * Check data in a forward traversal and overwrite it to (1-2-3-4-5).
 * Check new data in a backward traversal and release memory.
 * Violation: continue the backward traversal by following the circular link
 */
#include <stdlib.h>

typedef struct node {
  int data;
  struct node* next;
  struct node* prev;
} *DLL;

void myexit(int s) {
 _EXIT: goto _EXIT;
}

DLL dll_circular_create(int len, int data) {
  DLL last = (DLL) malloc(sizeof(struct node));
  if(NULL == last){
    myexit(1);
  }
  last->next = last;
  last->prev = last;
  last->data = data;
  DLL head = last;
  while(len > 1) {
    DLL new_head = (DLL) malloc(sizeof(struct node));
    if(NULL == new_head) {
      myexit(1);
    }
    new_head->next = head;
    new_head->data = data;
    head->prev = new_head;
    head = new_head;
    len--;
  }
  last->next = head;
  head->prev = last;
  return head;
}

int main() {
  const int len = 5;
  const int data_init = 1;
  DLL head = dll_circular_create(len, data_init);
  /* forward traversal */
  DLL ptr = head;
  int data_new = 1;
  do {
    if(data_init != ptr->data) {
      goto ERROR;
    }
    ptr->data = data_new;
    ptr = ptr->next;
    data_new++;
  } while(ptr != head);
  /* backward traversal */
  ptr = ptr->prev;
  /* Cause false-deref violation by not breaking the circle before the loop */
  /* head->prev = NULL; */
  head = NULL;
  do {
    data_new--;
    if(data_new != ptr->data) {
      goto ERROR;
    }
    DLL temp = ptr->prev;
    free(ptr);
    ptr = temp;
  } while(ptr != NULL);
  return 0; {reach_error();abort();}
 ERROR: return 1;
}
