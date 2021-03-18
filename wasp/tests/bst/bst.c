#include "mockups.h"

extern unsigned char __heap_base;
unsigned int bump_pointer = &__heap_base;

void* malloc(int n) {
  unsigned int r = bump_pointer;
  bump_pointer += n;
  return (void *)r;
}

void free(void* p) {
  // lol
}

#define FALSE 0
#define TRUE 1
#define NULL 0

typedef struct bstn {
    int value;
    struct bstn* left;
    struct bstn* right;
} BST;

BST* makeNode(int v) {
  BST* new_node = malloc(sizeof(BST));
  new_node->value = v;
  new_node->left = NULL;
  new_node->right = NULL;
  return new_node;
}


BST* insert(int v, BST* t) {
  if (t == NULL) {
    return makeNode(v);
  };
  if (v < t->value) {
    t->left = insert(v, t->left);
  } else if (v > t->value) {
    t->right = insert(v, t->right);
  };
  return t;
}


int find (int v, BST* t) {
  int ret;
  if (t == NULL) {
    ret = FALSE;
  } else if (v == t->value) {
    ret = TRUE;
  } else if (v < t->value) {
    ret = find(v, t->left);
  } else { /* the only last case is v > t->value */
    ret = find(v, t->right);
  }
  return ret;
}

int find_min (BST* t) {
  if (t->left == NULL) {
    return t->value;
  } else {
    return find_min(t->left);
  }
}

BST* remove(int v, BST* t) {
  BST* ret_node;
  if (t == NULL) {
    return NULL;
  } else if (v == t->value) {
    if (t->left == NULL) {
      ret_node = t->right;
      free(t);
      return ret_node;
    } else if (t->right == NULL) {
      ret_node = t->left;
      free(t);
      return ret_node;
    } else {
      int min = find_min(t->right);
      t->right = remove(min, t->right);
      t->value = min;
    }
  } else if (v < t->value) {
    t->left = remove(v, t->left);
  } else {
    t->right = remove(v, t->right);
  };
  return t;
}

int main()
{
    int a = dynamic_sym_int32('a');
    int b = dynamic_sym_int32('b');
    int e = dynamic_sym_int32('e');
    int f = dynamic_sym_int32('f');
    BST* bst = makeNode(a);
    bst = insert(b, bst);
    assume((e != a) && (e != b));
    assume((f == a) || (f == b));
    int isFalse = find(e, bst);
    int isTrue = find(f, bst);
    int c = dynamic_sym_int32('c');
    assume((c > a) && (a < b));
    bst = insert(c, bst);
    int isFalse2 = find_min(remove(b, bst)) == a;
    assert(!isFalse && isTrue && isFalse2);
    return 0;
}
