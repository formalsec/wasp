extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "float_req_bl_1092c.c", 3, "reach_error"); }

typedef int __int32_t;
typedef unsigned int __uint32_t;

typedef union {
  float value;
  __uint32_t word;
} ieee_float_shape_type;

static const float huge_ceil = 1.0e30;

float ceil_float(float x) {
  __int32_t i0, j0;
  __uint32_t i, ix;
  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (i0) = gf_u.word;
  } while (0);
  ix = (i0 & 0x7fffffff);
  j0 = (ix >> 23) - 0x7f;
  if (j0 < 23) {
    if (j0 < 0) {
      if (huge_ceil + x > (float)0.0) {
        if (i0 < 0) {
          i0 = 0x80000000;
        } else if (!((ix) == 0)) {
          i0 = 0x3f800000;
        }
      }
    } else {
      i = (0x007fffff) >> j0;
      if ((i0 & i) == 0)
        return x;
      if (huge_ceil + x > (float)0.0) {
        if (i0 > 0)
          i0 += (0x00800000) >> j0;
        i0 &= (~i);
      }
    }
  } else {
    if (!((ix) < 0x7f800000L))
      return x + x;
    else
      return x;
  }
  do {
    ieee_float_shape_type sf_u;
    sf_u.word = (i0);
    (x) = sf_u.value;
  } while (0);
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

  /*
   * REQ-BL-1092:
   * The ceil and ceilf procedures shall return the argument, if the argument x
   * is -+0 or -+Inf.
   */

  float x = 1.0f / 0.0f; // INF
  float res = ceil_float(x);

  // x is +inf , the result shall be +inf
  if (!isinf_float(res)) {
    {reach_error();}
    return 1;
  }

  return 0;
}
