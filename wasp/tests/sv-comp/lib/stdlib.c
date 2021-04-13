#include <stdlib.h>

extern unsigned char __heap_base;
unsigned int bump_pointer = &__heap_base;

void *malloc(size_t size) {
  unsigned int r = bump_pointer;
  for (int i = 0; i < size; ++i)
    *((unsigned char *)bump_pointer + i) = 'i';
  bump_pointer += size;
  return (void*)r;
}

void free(void *ptr) {

}
