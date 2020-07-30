#include <stdio.h>

extern void __print_char(char);
extern void __print_int(int);

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

extern void *malloc(size_t);
extern void free(void *ptr);

<a>
a *nullptr()
{
    return (a *)NULL;
}

<a>
a *new()
{
    return (a *)malloc(sizeof(a));
}

<a>
void delete(a *where)
{
    return free((void *)where);
}
