// CHM test source code

/*
 * This is pretty standard vector
 */
<T> // this is header -> instantiates types used in definition
struct vector {
    T *_content;
    int _length;
    int _capacity;
};

/*
 * Makes a vector of one element
 */
<T, V : V = struct vector /*: <T>*/> // commented not yet parsing (but it is a type unification)
V vectorise(T first) {
    V x;
    x._content = malloc(sizeof(T));
    x._length = 1;
    x._capacity = 1;

    if (x._content == NULL)  {
        exit(1);
    }

    x._content[0] = first;

    return x;
}

/*
 * if we say T is numeric, it has to be
 * - convertible from int
 * - addible to other T
 */
class Num <T> {
    T from_int(int a);
    T add(T a, T b); // or operator+ as in C++, C# etc.
    // etc...
}

instance Num <int> {
    int from_int(int a) { return a; }
    // etc...
}

/*
 * here we use types T and V and state that
 * V is vector of T and T is numeric
 * then V is also numeric (we can add two vectors)
 * vectorise(T) is a pseudo-call where all we care about is returned type
 */
<T, V : V = vectorise(T), Num<T> >
instance Num <V> {
    V from_int(int a) { return vectorise(from_int(a)); }
    // etc...
}

int main(void) {
    struct vector a = from_int(5); // a should be a vector of size 1 containing 5
    free_content(a);
    return 0;
}
