#ifndef PTHREAD_H
#define PTHREAD_H
struct _pthread_descr_struct {
  int empty;
};

typedef struct _pthread_descr_struct*_pthread_descr;
typedef int pthread_t;

/* Fast locks */
struct _pthread_fastlock { int __spinlock; };

#define PTHREAD_SPIN_LOCKED 1
#define PTHREAD_SPIN_UNLOCKED 0

/* Mutexes */
typedef struct {
  struct _pthread_fastlock lock;
  _pthread_descr owner;
  int kind;
  unsigned int count;
} pthread_mutex_t;

enum {
  PTHREAD_MUTEX_FAST_NP,
#define PTHREAD_MUTEX_FAST_NP PTHREAD_MUTEX_FAST_NP
  PTHREAD_MUTEX_RECURSIVE_NP,
#define PTHREAD_MUTEX_RECURSIVE_NP PTHREAD_MUTEX_RECURSIVE_NP
  PTHREAD_MUTEX_ERRORCHECK_NP,
#define PTHREAD_MUTEX_ERRORCHECK_NP PTHREAD_MUTEX_ERRORCHECK_NP
};

enum {
  PTHREAD_PROCESS_PRIVATE,
#define PTHREAD_PROCESS_PRIVATE PTHREAD_PROCESS_PRIVATE
  PTHREAD_PROCESS_SHARED
#define PTHREAD_PROCESS_SHARED PTHREAD_PROCESS_SHARED
};

#define PTHREAD_MUTEX_INITIALIZER \
{{PTHREAD_SPIN_UNLOCKED},0,PTHREAD_MUTEX_FAST_NP,0}

#define PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP \
{{PTHREAD_SPIN_UNLOCKED},0,PTHREAD_MUTEX_RECURSIVE_NP,0}

#define PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP \
{{PTHREAD_SPIN_UNLOCKED},0,PTHREAD_MUTEX_ERRORCHECK_NP,0}

typedef void* pthread_condattr_t;

typedef struct {
  struct _pthread_fastlock lock;
  _pthread_descr wait_chain;
} pthread_cond_t;

#define PTHREAD_COND_INITIALIZER \
{{PTHREAD_SPIN_UNLOCKED},0}

typedef int pthread_once_t;
#endif
