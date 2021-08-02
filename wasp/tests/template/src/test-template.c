#include <mockups.h>

typedef unsigned long size_t;

extern unsigned char __heap_base;
unsigned int bump_pointer = &__heap_base;

void *malloc(size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < size; ++i)
    *((unsigned char *)bump_pointer + i) = 'i';
  bump_pointer += size;
  return (void*)alloc(r, size);
}

void *calloc (size_t nmemb, size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < nmemb * size; ++i)
    *((unsigned int*)(bump_pointer + i)) = 0;
  bump_pointer += (nmemb * size);
  return (void *)alloc(r, nmemb * size);
}

void free(void *ptr) {
  dealloc(ptr);
}

void init_vector(int size) {
  int *arr = (int *)malloc(sizeof(int)*size);

  for (int i = 0; i < size; ++i) arr[i] = 0;

  free(arr);
}

int main() {
  
  int concrete = 10;
  int symbolic = sym_int("vector_size");
  assume (symbolic != 0);
  init_vector(concrete);
  init_vector(symbolic);
  return 0;
}
