#include <mockups.h>

int sym_int(char *name) {
  /* directly write WASM code */
  __asm__ __volatile__ ( 
      "local.get 0;"
      "drop;"
  );
  return 0;
}

void assume(int expr) {
  __asm__ __volatile__ (
      "local.get 0;"
      "drop;"
  );
}
void assert(int expr) {
  __asm__ __volatile__ (
      "local.get 0;"
      "drop;"
  );
}

void *alloc(void *ptr, unsigned int size) {
  return (void *) 0;
}

void dealloc(void *ptr) {

}
