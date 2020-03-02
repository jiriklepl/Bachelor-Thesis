# Name Mangling

## Functions

There can be only one function of the same name declared by one class and all its  definitions must differ at at least one parameter or the return value.

Mangling reflects this condition and assigns names by listing the following:

- Prefix: `_Z`
- Return value
- Name
- List of parameter type names

All names if not stated otherwise are prefixed by their length and optionally accompanied by symbols which signify that they are pointers.

## Structures, Unions and Enumerations

Mangling here is necessary as well... // TODO
