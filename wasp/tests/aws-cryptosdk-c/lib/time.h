#ifndef TIME_H
#define TIME_H

#include <sys/time.h>

#define CLOCK_REALTIME           0
#define CLOCK_MONOTONIC          1
#define CLOCK_PROCESS_CPUTIME_ID 2
#define CLOCK_THREAD_CPUTIME_ID  3
#define CLOCK_REALTIME_HR        4
#define CLOCK_MONOTONIC_HR       5

int clock_gettime(clockid_t clock_id,struct timespec*tp);

#endif

