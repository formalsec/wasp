#ifndef SUMMARIES_H_  
#define SUMMARIES_H_

#define STDIN 0

int strlen(char* s);
int strcmp(char* s1, char* s2);
int strncmp(char* s1, char* s2, int n);
char* strcpy(char* dest, char* source);
char* strncpy(char* dest, char* source, int n);
char* strcat(char* dest, char* source);

int puts(char* s);
int putchar(int c);
char getchar();
char* fgets(char *str, unsigned int length, void* stream);
int atoi(char *str);

#endif