#include <pthread.h>

int pthread_mutexattr_init(pthread_mutexattr_t*attr) {
  return 0;
}
int pthread_mutexattr_destroy(pthread_mutexattr_t*attr) {
  return 0;
}

int pthread_mutexattr_getkind_np(const pthread_mutexattr_t*attr,int*kind) {
  return 0;
}
int pthread_mutexattr_setkind_np(pthread_mutexattr_t*attr,int kind) {
  return 0;
}

int pthread_mutex_init(pthread_mutex_t*mutex,
    const pthread_mutexattr_t*mutexattr) {
  return 0;
}
int pthread_mutex_lock(pthread_mutex_t*mutex) {
  return 0;
}
int pthread_mutex_unlock(pthread_mutex_t*mutex) {
  return 0;
}
int pthread_mutex_trylock(pthread_mutex_t*mutex) {
  return 0;
}
int pthread_mutex_destroy(pthread_mutex_t*mutex) {
  return 0;
}

int pthread_mutexattr_settype(pthread_mutexattr_t *attr, int type) {
  return 0;
}

int pthread_rwlock_init(pthread_rwlock_t *rwlock, const pthread_rwlockattr_t *attr) {
  return 0;
}
int pthread_rwlock_destroy(pthread_rwlock_t *rwlock) {
  return 0;
}

int pthread_rwlock_rdlock(pthread_rwlock_t *rwlock) {
  return 0;
}
int pthread_rwlock_tryrdlock(pthread_rwlock_t *rwlock) {
  return 0;
}
int pthread_rwlock_wrlock(pthread_rwlock_t *rwlock) {
  return 0;
}
int pthread_rwlock_trywrlock(pthread_rwlock_t *rwlock) {
  return 0;
}
int pthread_rwlockattr_init(pthread_rwlockattr_t *attr) {
  return 0;
}
int pthread_rwlockattr_destroy(pthread_rwlockattr_t *attr) {
  return 0;
}
int pthread_rwlock_unlock(pthread_rwlock_t *rwlock) {
  return 0;
}
