extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "float_req_bl_0981.c", 3, "reach_error"); }

typedef int __int32_t;
typedef unsigned int __uint32_t;

typedef union {
  float value;
  __uint32_t word;
} ieee_float_shape_type;

static const float ln2_hi_log = 6.9313812256e-01, ln2_lo_log = 9.0580006145e-06,
                   two25_log = 3.355443200e+07, Lg1_log = 6.6666668653e-01,
                   Lg2_log = 4.0000000596e-01, Lg3_log = 2.8571429849e-01,
                   Lg4_log = 2.2222198546e-01, Lg5_log = 1.8183572590e-01,
                   Lg6_log = 1.5313838422e-01, Lg7_log = 1.4798198640e-01;

static const float zero_log = 0.0;

float __ieee754_logf(float x) {
  float hfsq, f, s, z, R, w, t1, t2, dk;
  __int32_t k, ix, i, j;

  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (ix) = gf_u.word;
  } while (0);

  k = 0;
  if (((ix & 0x7fffffff) == 0))
    return -two25_log / zero_log;
  if (ix < 0)
    return (x - x) / zero_log;
  if (!((ix) < 0x7f800000L))
    return x + x;
  if (((ix) < 0x00800000L)) {
    k -= 25;
    x *= two25_log;
    do {
      ieee_float_shape_type gf_u;
      gf_u.value = (x);
      (ix) = gf_u.word;
    } while (0);
  }
  k += (ix >> 23) - 127;
  ix &= 0x007fffff;
  i = (ix + (0x95f64 << 3)) & 0x800000;
  do {
    ieee_float_shape_type sf_u;
    sf_u.word = (ix | (i ^ 0x3f800000));
    (x) = sf_u.value;
  } while (0);
  k += (i >> 23);
  f = x - (float)1.0;
  if ((0x007fffff & (15 + ix)) < 16) {
    if (f == zero_log) {
      if (k == 0)
        return zero_log;
      else {
        dk = (float)k;
        return dk * ln2_hi_log + dk * ln2_lo_log;
      }
    }
    R = f * f * ((float)0.5 - (float)0.33333333333333333 * f);
    if (k == 0)
      return f - R;
    else {
      dk = (float)k;
      return dk * ln2_hi_log - ((R - dk * ln2_lo_log) - f);
    }
  }
  s = f / ((float)2.0 + f);
  dk = (float)k;
  z = s * s;
  i = ix - (0x6147a << 3);
  w = z * z;
  j = (0x6b851 << 3) - ix;
  t1 = w * (Lg2_log + w * (Lg4_log + w * Lg6_log));
  t2 = z * (Lg1_log + w * (Lg3_log + w * (Lg5_log + w * Lg7_log)));
  i |= j;
  R = t2 + t1;
  if (i > 0) {
    hfsq = (float)0.5 * f * f;
    if (k == 0)
      return f - (hfsq - s * (hfsq + R));
    else
      return dk * ln2_hi_log -
             ((hfsq - (s * (hfsq + R) + dk * ln2_lo_log)) - f);
  } else {
    if (k == 0)
      return f - s * (f - R);
    else
      return dk * ln2_hi_log - ((s * (f - R) - dk * ln2_lo_log) - f);
  }
}

static const float two25_log10 = 3.3554432000e+07,
                   ivln10_log10 = 4.3429449201e-01,
                   log10_2hi_log10 = 3.0102920532e-01,
                   log10_2lo_log10 = 7.9034151668e-07;

static const float zero = 0.0;

float __ieee754_log10f(float x) {
  float y, z;
  __int32_t i, k, hx;

  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (hx) = gf_u.word;
  } while (0);

  k = 0;
  if (((hx & 0x7fffffff) == 0))
    return -two25_log10 / zero;
  if (hx < 0)
    return (x - x) / zero;
  if (!((hx) < 0x7f800000L))
    return x + x;
  if (((hx) < 0x00800000L)) {
    k -= 25;
    x *= two25_log10;
    do {
      ieee_float_shape_type gf_u;
      gf_u.value = (x);
      (hx) = gf_u.word;
    } while (0);
  }
  k += (hx >> 23) - 127;
  i = ((__uint32_t)k & 0x80000000) >> 31;
  hx = (hx & 0x007fffff) | ((0x7f - i) << 23);
  y = (float)(k + i);
  do {
    ieee_float_shape_type sf_u;
    sf_u.word = (hx);
    (x) = sf_u.value;
  } while (0);
  z = y * log10_2lo_log10 + ivln10_log10 * __ieee754_logf(x);
  return z + y * log10_2hi_log10;
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
   * REQ-BL-0981
   * The log10 and log10f procedures shall return +Inf, if the argument x is
   * +Inf .
   */

  float x = 1.0f / 0.0f; // INF
  float res = __ieee754_log10f(x);

  // x is +inf, result shall be +inf
  if (!isinf_float(res)) {
    {reach_error();}
    return 1;
  }
  return 0;
}
