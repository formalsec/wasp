#include "assert.h"
#include <openssl/evp.h>

extern int nondet_int(void);

const EVP_MD *nondet_EVP_MD_ptr(void) {
  return 0;
}
const EVP_CIPHER *nondet_EVP_CIPHER_ptr(void) {
  return 0;
}
