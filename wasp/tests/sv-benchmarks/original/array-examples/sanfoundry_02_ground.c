extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int();

/*
 * Adapted from http://www.sanfoundry.com/c-programming-examples-arrays/
 * C program to read in four integer numbers into an array and find the
 * average of largest two of the given numbers without sorting the array.
 * The program should output the given four numbers and the average.
 */
#define MAX 100000 
 
int main()
{
    int array[MAX];
    int i;
    int largest1;
    int largest2;
    int temp;
		
		for(i = 0; i < MAX; i++) 
		{
		  array[i] = __VERIFIER_nondet_int();
		}
 
    /*  assume first element of array is the first larges t*/
    largest1 = array[0];
    /*  assume first element of array is the second largest */
    largest2 = array[1];

    if (largest1 < largest2)
    {
        temp = largest1;
        largest1 = largest2;
        largest2 = temp;
    }
    for (i = 2; i < MAX;  i++)
    {
        if (array[i] >= largest1)
        {
            largest2 = largest1;
            largest1 = array[i];
        }
        else if (array[i] > largest2)
        {
            largest2 = array[i];
        }
    }
    
    int x;
    for( x = 0 ; x < MAX ; x++ ) {
      __VERIFIER_assert(  array[ x ] <= largest1  );
    }
    for( x = 0 ; x < MAX ; x++ ) {
      __VERIFIER_assert(  array[x] <= largest2 || array[x] == largest1  );
    }
  return 0;
}
