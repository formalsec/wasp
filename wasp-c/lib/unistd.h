#ifndef UNISTD_H
#define UNISTD_H

#include <sys/types.h>

int open(const char* pathname,int flags, ...);
int close(int fd);
ssize_t read(int fd,void* buf,size_t len);

#endif
