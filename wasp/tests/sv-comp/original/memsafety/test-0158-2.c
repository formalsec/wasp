extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

#include <stdlib.h>

int main()
{
    union {
        void *p0;

        struct {
            char c[2];
            void *p1;
            void *p2;
        } str;

    } data;

    // alloc 37B on heap
    data.p0 = malloc(37U);

    // this should be fine
    data.str.p2 = &data;

    // this introduces a memleak
    data.str.c[1] = sizeof data.str.p1;

    return 0;
}
