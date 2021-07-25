extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "double_req_bl_0920b.c", 3, "reach_error"); }
extern double __VERIFIER_nondet_double();

typedef int __int32_t;
typedef unsigned int __uint32_t;

/* A union which permits us to convert between a double and two 32 bit
   ints.  */
typedef union {
  double value;
  struct {
    __uint32_t lsw;
    __uint32_t msw;
  } parts;
} ieee_double_shape_type;

// infinity check for doubles
int isinf_double(double x) {
  __int32_t hx, lx;
  do {
    ieee_double_shape_type ew_u;
    ew_u.value = (x);
    (hx) = ew_u.parts.msw;
    (lx) = ew_u.parts.lsw;
  } while (0);
  hx &= 0x7fffffff;
  hx |= (__uint32_t)(lx | (-lx)) >> 31;
  hx = 0x7ff00000 - hx;
  return 1 - (int)((__uint32_t)(hx | (-hx)) >> 31);
}

static const double ln2_hi_log = 6.93147180369123816490e-01,
                    ln2_lo_log = 1.90821492927058770002e-10,
                    two54_log = 1.80143985094819840000e+16,
                    Lg1_log = 6.666666666666735130e-01,
                    Lg2_log = 3.999999999940941908e-01,
                    Lg3_log = 2.857142874366239149e-01,
                    Lg4_log = 2.222219843214978396e-01,
                    Lg5_log = 1.818357216161805012e-01,
                    Lg6_log = 1.531383769920937332e-01,
                    Lg7_log = 1.479819860511658591e-01;

static const double zero = 0.0;

double __ieee754_log(double x) {
  double hfsq, f, s, z, R, w, t1, t2, dk;
  __int32_t k, hx, i, j;
  __uint32_t lx;

  do {
    ieee_double_shape_type ew_u;
    ew_u.value = (x);
    (hx) = ew_u.parts.msw;
    (lx) = ew_u.parts.lsw;
  } while (0);

  k = 0;
  if (hx < 0x00100000) {
    if (((hx & 0x7fffffff) | lx) == 0)
      return -two54_log / zero;
    if (hx < 0)
      return (x - x) / zero;
    k -= 54;
    x *= two54_log;
    do {
      ieee_double_shape_type gh_u;
      gh_u.value = (x);
      (hx) = gh_u.parts.msw;
    } while (0);
  }
  if (hx >= 0x7ff00000)
    return x + x;
  k += (hx >> 20) - 1023;
  hx &= 0x000fffff;
  i = (hx + 0x95f64) & 0x100000;
  do {
    ieee_double_shape_type sh_u;
    sh_u.value = (x);
    sh_u.parts.msw = (hx | (i ^ 0x3ff00000));
    (x) = sh_u.value;
  } while (0);
  k += (i >> 20);
  f = x - 1.0;
  if ((0x000fffff & (2 + hx)) < 3) {
    if (f == zero) {
      if (k == 0)
        return zero;
      else {
        dk = (double)k;
        return dk * ln2_hi_log + dk * ln2_lo_log;
      }
    }
    R = f * f * (0.5 - 0.33333333333333333 * f);
    if (k == 0)
      return f - R;
    else {
      dk = (double)k;
      return dk * ln2_hi_log - ((R - dk * ln2_lo_log) - f);
    }
  }
  s = f / (2.0 + f);
  dk = (double)k;
  z = s * s;
  i = hx - 0x6147a;
  w = z * z;
  j = 0x6b851 - hx;
  t1 = w * (Lg2_log + w * (Lg4_log + w * Lg6_log));
  t2 = z * (Lg1_log + w * (Lg3_log + w * (Lg5_log + w * Lg7_log)));
  i |= j;
  R = t2 + t1;
  if (i > 0) {
    hfsq = 0.5 * f * f;
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

int isfinite_double(double x) {
  __int32_t hx;
  do {
    ieee_double_shape_type gh_u;
    gh_u.value = (x);
    (hx) = gh_u.parts.msw;
  } while (0);
  return (int)((__uint32_t)((hx & 0x7fffffff) - 0x7ff00000) >> 31);
}

// nan check for doubles
int isnan_double(double x) { return x != x; }

int main() {

  /* REQ-BL-0920
   * The log and logf procedures shall return NaN if the argument x is finite
   * and less than 0 or x is -Inf.
   */

  double x = -1.0 / 0.0; // -INF
  double res = __ieee754_log(x);

  // x is -inf, result shall be NAN
  if (!isnan_double(res)) {
    {reach_error();}
    return 1;
  }

  return 0;
}
