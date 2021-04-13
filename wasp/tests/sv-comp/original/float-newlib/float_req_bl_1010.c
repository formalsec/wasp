extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "float_req_bl_1010.c", 3, "reach_error"); }
extern float __VERIFIER_nondet_float();

typedef int __int32_t;
typedef unsigned int __uint32_t;

typedef union {
  float value;
  __uint32_t word;
} ieee_float_shape_type;

int isnan_float(float x) { return x != x; }

float fabs_float(float x) {
  __uint32_t ix;
  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (ix) = gf_u.word;
  } while (0);
  do {
    ieee_float_shape_type sf_u;
    sf_u.word = (ix & 0x7fffffff);
    (x) = sf_u.value;
  } while (0);
  return x;
}

int main() {

  /* REQ-BL-1010
   * The fabs and fabsf procedures shall return NaN , if the argument x is NaN.
   */

  float x = 0.0f / 0.0f; // NAN
  float res = fabs_float(x);

  // x is NAN, result shall be NAN
  if (!isnan_float(res)) {
    {reach_error();}
    return 1;
  }

  return 0;
}
