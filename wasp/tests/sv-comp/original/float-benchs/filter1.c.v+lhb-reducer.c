int __return_main;
void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "filter1.c.v+lhb-reducer.c", 4, "reach_error"); }
int __VERIFIER_nondet_int();
double __VERIFIER_nondet_double();
void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond);
int main();
int __tmp_129_0;
int __tmp_129_1;
int __tmp_129_2;
int __return_134;
 int main()
 {
 double main__E0;
 double main__E1;
 double main__S;
 int main__i;
 main__E1 = 0;
 main__S = 0;
 main__i = 0;
 if (main__i <= 1000000)
 {
 main__E0 = __VERIFIER_nondet_double();
 int main____CPAchecker_TMP_0;
 if (main__E0 >= -1.0)
 {
 if (main__E0 <= 1.0)
 {
 main____CPAchecker_TMP_0 = 1;
 if (main____CPAchecker_TMP_0 != 0)
 {
 int main____CPAchecker_TMP_1;
 main____CPAchecker_TMP_1 = __VERIFIER_nondet_int();
 if (!(main____CPAchecker_TMP_1 == 0))
 {
 main__S = 0;
 label_118:; 
 main__E1 = main__E0;
 int main____CPAchecker_TMP_2;
 if (main__S >= -10000.0)
 {
 if (main__S <= 10000.0)
 {
 main____CPAchecker_TMP_2 = 1;
 label_123:; 
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
 __tmp_129_0 = main____CPAchecker_TMP_2;
 __tmp_129_1 = main____CPAchecker_TMP_1;
 __tmp_129_2 = main____CPAchecker_TMP_0;
 label_129:; 
 main____CPAchecker_TMP_2 = __tmp_129_0;
 main____CPAchecker_TMP_1 = __tmp_129_1;
 main____CPAchecker_TMP_0 = __tmp_129_2;
 main__i = main__i + 1;
 if (main__i <= 1000000)
 {
 main__E0 = __VERIFIER_nondet_double();
 int main____CPAchecker_TMP_0;
 if (main__E0 >= -1.0)
 {
 if (main__E0 <= 1.0)
 {
 main____CPAchecker_TMP_0 = 1;
 label_139:; 
 if (main____CPAchecker_TMP_0 != 0)
 {
 int main____CPAchecker_TMP_1;
 main____CPAchecker_TMP_1 = __VERIFIER_nondet_int();
 if (!(main____CPAchecker_TMP_1 == 0))
 {
 main__S = 0;
 label_147:; 
 main__E1 = main__E0;
 int main____CPAchecker_TMP_2;
 if (main__S >= -10000.0)
 {
 if (main__S <= 10000.0)
 {
 main____CPAchecker_TMP_2 = 1;
 label_152:; 
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
 __tmp_129_0 = main____CPAchecker_TMP_2;
 __tmp_129_1 = main____CPAchecker_TMP_1;
 __tmp_129_2 = main____CPAchecker_TMP_0;
 goto label_129;
 }
 }
 }
 else 
 {
 label_151:; 
 main____CPAchecker_TMP_2 = 0;
 goto label_152;
 }
 }
 else 
 {
 goto label_151;
 }
 }
 else 
 {
 main__S = ((0.999 * main__S) + main__E0) - main__E1;
 goto label_147;
 }
 }
 else 
 {
 return __return_main;
 }
 }
 else 
 {
 label_138:; 
 main____CPAchecker_TMP_0 = 0;
 goto label_139;
 }
 }
 else 
 {
 goto label_138;
 }
 }
 else 
 {
  __return_134 = 0;
 return __return_134;
 }
 }
 }
 }
 else 
 {
 label_122:; 
 main____CPAchecker_TMP_2 = 0;
 goto label_123;
 }
 }
 else 
 {
 goto label_122;
 }
 }
 else 
 {
 main__S = ((0.999 * main__S) + main__E0) - main__E1;
 goto label_118;
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
 else 
 {
 return __return_main;
 }
 }
