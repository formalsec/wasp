extern void abort(void);

extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "float22.c", 3, __extension__ __PRETTY_FUNCTION__); })); }






typedef signed char int8_t;
typedef short int int16_t;
typedef int int32_t;



__extension__
typedef long long int int64_t;




typedef unsigned char uint8_t;
typedef unsigned short int uint16_t;

typedef unsigned int uint32_t;





__extension__
typedef unsigned long long int uint64_t;






typedef signed char int_least8_t;
typedef short int int_least16_t;
typedef int int_least32_t;



__extension__
typedef long long int int_least64_t;



typedef unsigned char uint_least8_t;
typedef unsigned short int uint_least16_t;
typedef unsigned int uint_least32_t;



__extension__
typedef unsigned long long int uint_least64_t;






typedef signed char int_fast8_t;





typedef int int_fast16_t;
typedef int int_fast32_t;
__extension__
typedef long long int int_fast64_t;



typedef unsigned char uint_fast8_t;





typedef unsigned int uint_fast16_t;
typedef unsigned int uint_fast32_t;
__extension__
typedef unsigned long long int uint_fast64_t;
typedef int intptr_t;


typedef unsigned int uintptr_t;
__extension__
typedef long long int intmax_t;
__extension__
typedef unsigned long long int uintmax_t;

typedef struct _components {
  unsigned int negative:1;
  unsigned int exponent:8;
  unsigned int mantissa:23;
} components;

typedef union _ieee754_float {
  components ieee;
  float f;
} ieee754_float;


float returnsField (uint32_t index) {
    ieee754_float c;

    c.ieee.negative = index & 0x1;
    c.ieee.exponent = 0;
    c.ieee.mantissa = 0;

    return c.f;
}

ieee754_float returnsStructure (uint32_t index) {
    ieee754_float c;

    c.ieee.negative = index & 0x1;
    c.ieee.exponent = 0;
    c.ieee.mantissa = 0;

    return c;
}


void testOne (void) {
   ieee754_float f1, f2;

   f1 = returnsStructure(0);
   f2 = returnsStructure(1);

   if(!(f1.ieee.negative != f2.ieee.negative)) {reach_error();abort();}

   return;
}


void testTwo (void) {
   ieee754_float f1, f2;

   f1 = returnsStructure(0);
   f2 = returnsStructure(1);

   if(!(f1.ieee.negative != f2.ieee.negative)) {reach_error();abort();}

   f1.f = returnsField(0);
   f2.f = returnsField(1);

   if(!(f1.ieee.negative != f2.ieee.negative)) {reach_error();abort();}

   return;
}


int testThree (void) {
   ieee754_float f1, f2;

   f1.f = returnsField(0);
   f2.f = returnsField(1);

   if(!(f1.ieee.negative != f2.ieee.negative)) {reach_error();abort();}

   return 1;
}

int main (void) {
  testOne();
  testTwo();
  testThree();

  return 0;
}
