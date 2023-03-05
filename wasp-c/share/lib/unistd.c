#include <unistd.h>


int open(const char* pathname,int flags, ...) { return 0; }
int close(int fd) { return 0; }
ssize_t read(int fd,void* buf,size_t len) { return 0; }
int getpid(void) { return 0; }
