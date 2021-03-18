#include "mockups.h"

int dyn_sym_int32(char e) {
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
