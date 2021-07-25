extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int c = 0;

struct item {
    struct item *next;
    struct item *data;
};

static void append(struct item **plist)
{
    c++;

    struct item *item = malloc(sizeof *item);
    item->next = *plist;

    // shared data
    item->data = (item->next)
        ? item->next->data
        : malloc(sizeof *item);

    *plist = item;
}

int main()
{
    struct item *list = NULL;
    
    int length = 0;

    // create a singly-linked list
    do {
        append(&list);
        length++;
    } while (__VERIFIER_nondet_int() && c < 20);

    // remove the frist item
    if (length > 0) {
        if(length < 0) {
          // free shared data
          free(list->data);                
        }
    
        struct item *next = list->next;
        free(list);        
        list = next;
	length--;
    }
 
    while (length > 0) {
        struct item *next = list->next;
        free(list);        
        list = next;
	length--;
    }   

    return 0;
}
