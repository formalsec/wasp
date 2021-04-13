/*

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

/* Program Description :-
 * A square 2D array is declared.
 * Elements of matrix are initialized as the following condition :-
 * i) If main diagonal element, assign zero.
 * ii) Otherwise, assign column number.
 * Sum of array should be (1/2)*(ARR_SIZE)*(ARR_SIZE-1)^2.
 * ARR_SIZE.
 */
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array29_pattern.c", 26, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int() ;
extern short __VERIFIER_nondet_short() ;

signed long long ARR_SIZE ;


int main()
{
	ARR_SIZE = (signed long long)__VERIFIER_nondet_short() ;
	assume_abort_if_not(ARR_SIZE > 1) ;

	int array[ARR_SIZE][ARR_SIZE] ;
	
	int row = 0, column = 0 ;
       	signed long long sum = 0 ;

	for(row=0;row<ARR_SIZE;row++)
		for(column=0;column<ARR_SIZE;column++)
		{
			if(row == column)
				array[row][row] = 0 ;
			else
				array[row][column] = column ;
		}
				

	for(row=0;row<ARR_SIZE;row++)
		for(column=0;column<ARR_SIZE;column++)
			sum = sum + array[row][column] ;

	__VERIFIER_assert(2*sum == (ARR_SIZE*(ARR_SIZE-1)*(ARR_SIZE-1))) ;
	return 0 ;
}
