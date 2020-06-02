void *NULL = (void*)0;

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
