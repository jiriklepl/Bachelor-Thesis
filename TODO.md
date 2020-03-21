# TODO

- add chm header-calls (like `vector<int>` in c++, java etc.)
- `tiProgram initialEnv ["I" :>: toScheme tInt] [([],[[("hohoo", [([],Var "I")])]])]`
- consider implementing class `HasDefault<Type>` as in C it is allowed to have `main` return nothing and `0` (int's default value) is returned
- do CCast
- do CSizeofExpr, ditto for Type and double-ditto for align
- do CComplexReal and CComplexImag
- there is a problem with `main(void){}`
- change return to bind the real return value
- support `int x = value;`
