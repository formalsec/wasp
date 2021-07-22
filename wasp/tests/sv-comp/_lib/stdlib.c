#include "stdlib.h"

extern unsigned char __heap_base;
unsigned int bump_pointer = &__heap_base;


void *malloc(size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < size; ++i)
    *((unsigned char *)bump_pointer + i) = 'i';
  bump_pointer += size;
  return (void*)alloc(r, size);
}

void *alloca(size_t size) {
  return malloc(size);
}

void *calloc (size_t nmemb, size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < nmemb * size; ++i)
    *((unsigned int*)(bump_pointer + i)) = 0;
  bump_pointer += (nmemb * size);
  return (void *)alloc(r, nmemb * size);
}

void *realloc(void *ptr, size_t size) {
  dealloc(ptr);
  return (void *)alloc(ptr, size);
}

void free(void *ptr) {
  dealloc(ptr);
}
 
