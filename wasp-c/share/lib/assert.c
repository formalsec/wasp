#include "assert.h"
#include "wasp.h"

void assert(int expr) {
  return __WASP_assert(expr);
}

