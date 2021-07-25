
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "float_req_bl_1072a.c", 4, "reach_error"); }

typedef int __int32_t;
typedef unsigned int __uint32_t;

typedef union {
  float value;
  __uint32_t word;
} ieee_float_shape_type;

float trunc_float(float x) {
  __int32_t signbit, w, exponent_less_127;
  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (w) = gf_u.word;
  } while (0);
  signbit = w & 0x80000000;
  exponent_less_127 = ((w & 0x7f800000) >> 23) - 127;
  if (exponent_less_127 < 23) {
    if (exponent_less_127 < 0) {

      do {
        ieee_float_shape_type sf_u;
        sf_u.word = (signbit);
        (x) = sf_u.value;
      } while (0);
    } else {
      do {
        ieee_float_shape_type sf_u;
        sf_u.word = (signbit | (w & ~(0x007fffff >> exponent_less_127)));
        (x) = sf_u.value;
      } while (0);
    }
  } else {
    if (exponent_less_127 == 255)
      return x + x;
  }
  return x;
}

// infinity check for floats
int isinf_float(float x) {
  __int32_t ix;
  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (ix) = gf_u.word;
  } while (0);
  ix &= 0x7fffffff;
  return ((ix) == 0x7f800000L);
}

int main() {

  /* REQ-BL-1072
   * The trunc and truncf procedures shall return the argument, if the argument
   * x is +-0 or +-Inf .
   */

  float x = 1.0f / 0.0f; // INF
  float res = trunc_float(x);

  // x is inf, result shall be inf
  if (!isinf_float(res)) {
    {reach_error();}
    return 1;
  }

  return 0;
}
