extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "float_req_bl_0621b.c", 3, "reach_error"); }
extern float __VERIFIER_nondet_float();

typedef int __int32_t;
typedef unsigned int __uint32_t;

typedef union {
  float value;
  __uint32_t word;
} ieee_float_shape_type;

static const float huge_floor = 1.0e30;

// nan check for floats
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

static const float atanhi_atan[] = {
    4.6364760399e-01,
    7.8539812565e-01,
    9.8279368877e-01,
    1.5707962513e+00,
};

static const float atanlo_atan[] = {
    5.0121582440e-09,
    3.7748947079e-08,
    3.4473217170e-08,
    7.5497894159e-08,
};

static const float aT_atan[] = {
    3.3333334327e-01, -2.0000000298e-01, 1.4285714924e-01, -1.1111110449e-01,
    9.0908870101e-02, -7.6918758452e-02, 6.6610731184e-02, -5.8335702866e-02,
    4.9768779427e-02, -3.6531571299e-02, 1.6285819933e-02,
};

static const float one_atan = 1.0, huge_atan = 1.0e30,
                   pi_o_4 = 7.8539818525e-01, pi_o_2 = 1.5707963705e+00,
                   pi = 3.1415927410e+00;

float atan_float(float x) {
  float w, s1, s2, z;
  __int32_t ix, hx, id;

  do {
    ieee_float_shape_type gf_u;
    gf_u.value = (x);
    (hx) = gf_u.word;
  } while (0);
  ix = hx & 0x7fffffff;
  if (ix >= 0x50800000) {
    if (((ix) > 0x7f800000L))
      return x + x;
    if (hx > 0)
      return atanhi_atan[3] + atanlo_atan[3];
    else
      return -atanhi_atan[3] - atanlo_atan[3];
  }
  if (ix < 0x3ee00000) {
    if (ix < 0x31000000) {
      if (huge_atan + x > one_atan)
        return x;
    }
    id = -1;
  } else {
    x = fabs_float(x);
    if (ix < 0x3f980000) {
      if (ix < 0x3f300000) {
        id = 0;
        x = ((float)2.0 * x - one_atan) / ((float)2.0 + x);
      } else {
        id = 1;
        x = (x - one_atan) / (x + one_atan);
      }
    } else {
      if (ix < 0x401c0000) {
        id = 2;
        x = (x - (float)1.5) / (one_atan + (float)1.5 * x);
      } else {
        id = 3;
        x = -(float)1.0 / x;
      }
    }
  }

  z = x * x;
  w = z * z;

  s1 = z * (aT_atan[0] +
            w * (aT_atan[2] +
                 w * (aT_atan[4] +
                      w * (aT_atan[6] + w * (aT_atan[8] + w * aT_atan[10])))));
  s2 =
      w *
      (aT_atan[1] +
       w * (aT_atan[3] + w * (aT_atan[5] + w * (aT_atan[7] + w * aT_atan[9]))));
  if (id < 0)
    return x - x * (s1 + s2);
  else {
    z = atanhi_atan[id] - ((x * (s1 + s2) - atanlo_atan[id]) - x);
    return (hx < 0) ? -z : z;
  }
}

int main() {

  /* REQ-BL-0621:
   * The atan and atanf procedures shall return +-pi/2 if the argument is +-Inf.
   */

  float x = -1.0f / 0.0f; // -INF
  float res = atan_float(x);
  // x is +-inf the result shall be +-pi/2
  if (res != -pi_o_2) {
    {reach_error();}
    return 1;
  }

  return 0;
}
