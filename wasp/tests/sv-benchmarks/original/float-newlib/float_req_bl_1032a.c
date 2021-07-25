extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "float_req_bl_1032a.c", 3, "reach_error"); }
extern float __VERIFIER_nondet_float();

typedef int __int32_t;
typedef unsigned int __uint32_t;

typedef union {
  float value;
  __uint32_t word;
} ieee_float_shape_type;

float round_float(float x) {
  __uint32_t w;

  int exponent_less_127;

  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (w) = gf_u.word;
  } while (0);

  exponent_less_127 = (int)((w & 0x7f800000) >> 23) - 127;

  if (exponent_less_127 < 23) {
    if (exponent_less_127 < 0) {
      w &= 0x80000000;
      if (exponent_less_127 == -1)

        w |= ((__uint32_t)127 << 23);
    } else {
      unsigned int exponent_mask = 0x007fffff >> exponent_less_127;
      if ((w & exponent_mask) == 0)

        return x;

      w += 0x00400000 >> exponent_less_127;
      w &= ~exponent_mask;
    }
  } else {
    if (exponent_less_127 == 128)

      return x + x;
    else
      return x;
  }
  do {
    ieee_float_shape_type sf_u;
    sf_u.word = (w);
    (x) = sf_u.value;
  } while (0);
  return x;
}

int __signbit_float(float x) {
  __uint32_t w;

  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (w) = gf_u.word;
  } while (0);

  return (w & 0x80000000) != 0;
}

int main() {

  /*
   * REQ-BL-1032//GTD-TR-01-BL-0015, GTD-TR-01-BL-0026/T
   * The round and roundf procedures shall return the argument, if the argument
   * x is +-0 or +-Inf .
   */

  float x = 0.0f;
  float res = round_float(x);

  // result shall be x
  if (!(res == 0.0f && __signbit_float(res) == 0)) {
    {reach_error();}
    return 1;
  }

  return 0;
}
