# TODO

- add chm header-calls (like `vector<int>` in c++, java etc.)
- consider implementing class `HasDefault<Type>` as in C it is allowed to have `main` return nothing and `0` (int's default value) is returned
- do CCast
- do CSizeofExpr, ditto for Type and double-ditto for align
- do CComplexReal and CComplexImag
- there is a problem with `main(void){}`
- look at why it doesn't parse C-structs when there are no instances given in the struct definition
- consider looking at whether to make a dedicated function that would transform class constraints (instead of repeated manual checking of count of parameter)
