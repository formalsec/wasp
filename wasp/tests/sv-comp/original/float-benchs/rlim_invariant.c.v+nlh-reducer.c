int __return_main;
void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "rlim_invariant.c.v+nlh-reducer.c", 4, "reach_error"); }
float __VERIFIER_nondet_float();
void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond);
int main();
int __tmp_160_0;
int __tmp_160_1;
int __tmp_160_2;
int __tmp_142_0;
int __tmp_142_1;
int __tmp_136_0;
int __return_165;
 int main()
 {
 float main__X;
 float main__Y;
 float main__S;
 float main__R;
 float main__D;
 int main__i;
 main__Y = 0;
 main__i = 0;
 if (main__i < 100000)
 {
 main__X = __VERIFIER_nondet_float();
 main__D = __VERIFIER_nondet_float();
 int main____CPAchecker_TMP_0;
 if (main__X >= -128.0)
 {
 if (main__X <= 128.0)
 {
 main____CPAchecker_TMP_0 = 1;
 if (main____CPAchecker_TMP_0 != 0)
 {
 int main____CPAchecker_TMP_1;
 if (main__D >= 0.0)
 {
 if (main__D <= 16.0)
 {
 main____CPAchecker_TMP_1 = 1;
 if (main____CPAchecker_TMP_1 != 0)
 {
 main__S = main__Y;
 main__Y = main__X;
 main__R = main__X - main__S;
 if (main__R <= (-main__D))
 {
 main__Y = main__S - main__D;
 label_150:; 
 int main____CPAchecker_TMP_2;
 if (main__Y >= -129.0)
 {
 if (main__Y <= 129.0)
 {
 main____CPAchecker_TMP_2 = 1;
 label_154:; 
 {
 int __tmp_1;
 __tmp_1 = main____CPAchecker_TMP_2;
 int __VERIFIER_assert__cond;
 __VERIFIER_assert__cond = __tmp_1;
 if (__VERIFIER_assert__cond == 0)
 {
 {reach_error();}
 return __return_main;
 }
 else 
 {
 __tmp_160_0 = main____CPAchecker_TMP_0;
 __tmp_160_1 = main____CPAchecker_TMP_1;
 __tmp_160_2 = main____CPAchecker_TMP_2;
 label_160:; 
 main____CPAchecker_TMP_0 = __tmp_160_0;
 main____CPAchecker_TMP_1 = __tmp_160_1;
 main____CPAchecker_TMP_2 = __tmp_160_2;
 main__i = main__i + 1;
 if (main__i < 100000)
 {
 main__X = __VERIFIER_nondet_float();
 main__D = __VERIFIER_nondet_float();
 int main____CPAchecker_TMP_0;
 if (main__X >= -128.0)
 {
 if (main__X <= 128.0)
 {
 main____CPAchecker_TMP_0 = 1;
 label_171:; 
 if (main____CPAchecker_TMP_0 != 0)
 {
 int main____CPAchecker_TMP_1;
 if (main__D >= 0.0)
 {
 if (main__D <= 16.0)
 {
 main____CPAchecker_TMP_1 = 1;
 label_176:; 
 if (main____CPAchecker_TMP_1 != 0)
 {
 main__S = main__Y;
 main__Y = main__X;
 main__R = main__X - main__S;
 if (main__R <= (-main__D))
 {
 main__Y = main__S - main__D;
 label_185:; 
 int main____CPAchecker_TMP_2;
 if (main__Y >= -129.0)
 {
 if (main__Y <= 129.0)
 {
 main____CPAchecker_TMP_2 = 1;
 label_189:; 
 {
 int __tmp_2;
 __tmp_2 = main____CPAchecker_TMP_2;
 int __VERIFIER_assert__cond;
 __VERIFIER_assert__cond = __tmp_2;
 if (__VERIFIER_assert__cond == 0)
 {
 {reach_error();}
 return __return_main;
 }
 else 
 {
 __tmp_160_0 = main____CPAchecker_TMP_0;
 __tmp_160_1 = main____CPAchecker_TMP_1;
 __tmp_160_2 = main____CPAchecker_TMP_2;
 goto label_160;
 }
 }
 }
 else 
 {
 label_188:; 
 main____CPAchecker_TMP_2 = 0;
 goto label_189;
 }
 }
 else 
 {
 goto label_188;
 }
 }
 else 
 {
 if (main__R >= main__D)
 {
 main__Y = main__S + main__D;
 goto label_185;
 }
 else 
 {
 goto label_185;
 }
 }
 }
 else 
 {
 __tmp_142_0 = main____CPAchecker_TMP_0;
 __tmp_142_1 = main____CPAchecker_TMP_1;
 label_142:; 
 main____CPAchecker_TMP_0 = __tmp_142_0;
 main____CPAchecker_TMP_1 = __tmp_142_1;
 return __return_main;
 }
 }
 else 
 {
 label_175:; 
 main____CPAchecker_TMP_1 = 0;
 goto label_176;
 }
 }
 else 
 {
 goto label_175;
 }
 }
 else 
 {
 __tmp_136_0 = main____CPAchecker_TMP_0;
 label_136:; 
 main____CPAchecker_TMP_0 = __tmp_136_0;
 return __return_main;
 }
 }
 else 
 {
 label_170:; 
 main____CPAchecker_TMP_0 = 0;
 goto label_171;
 }
 }
 else 
 {
 goto label_170;
 }
 }
 else 
 {
  __return_165 = 0;
 return __return_165;
 }
 }
 }
 }
 else 
 {
 label_153:; 
 main____CPAchecker_TMP_2 = 0;
 goto label_154;
 }
 }
 else 
 {
 goto label_153;
 }
 }
 else 
 {
 if (main__R >= main__D)
 {
 main__Y = main__S + main__D;
 goto label_150;
 }
 else 
 {
 goto label_150;
 }
 }
 }
 else 
 {
 __tmp_142_0 = main____CPAchecker_TMP_0;
 __tmp_142_1 = main____CPAchecker_TMP_1;
 goto label_142;
 }
 }
 else 
 {
 return __return_main;
 }
 }
 else 
 {
 return __return_main;
 }
 }
 else 
 {
 __tmp_136_0 = main____CPAchecker_TMP_0;
 goto label_136;
 }
 }
 else 
 {
 return __return_main;
 }
 }
 else 
 {
 return __return_main;
 }
 }
 else 
 {
 return __return_main;
 }
 }
