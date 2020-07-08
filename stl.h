#include <stdio.h>

void __print_char(char);
void __print_int(int);

<a>
class Print {
    void print(a *);
}

instance Print<char> {
    void print(char *a)
    {
        __print_char(*a);
    }
}

instance Print<int> {
    void print(int *a)
    {
        __print_int(*a);
    }
}

extern void *malloc(int);
extern void free(void *ptr);

<a>
a *nullptr()
{
    return (a*)NULL;
}

<a>
a *new()
{
    return (a*)malloc(sizeof(a));
}

<a>
void delete(a* where)
{
    return free((void *)where);
}

<a>
a* newArray(int x)
{}

<a>
void deleteArray(a* x)
{}
