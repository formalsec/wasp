#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <proof_helpers/nondet.h>

void __CPROVER_assume(bool assumption) { 
  assume(assumption);
}

void __CPROVER_assert(bool assertion, const char *description) { 
  assert(assertion);
}

size_t __CPROVER_OBJECT_SIZE(const void *p) {
  return sizeof(p);
}
