#include "libc_summaries.h"
#include "api.h"

int main(){

	int four = 4;
	char s[] = "test";

  int len = strlen(s);

	//len should be 4
	summ_print_restriction(_solver_EQ(&len, &four, 32)); //True

	return 0;
}
