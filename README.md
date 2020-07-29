# CHM Compiler

This program compiles programs written in the CHM language. For the proposal of the language, see the bachelor thesis repository [Bachelor-Thesis-Text](https://github.com/jiriklepl/Bachelor-Thesis-Text).

The purpose of this compiler is to demonstrate the possibility of implementing an alternative to the C language which uses a variant of the Hindley-Milner type system. This language aims to preserve the core nature of the C language: explicit memory management, high level of code transparency, and giving the user control over almost all computations the program performs (= minimal runtime overhead).

## Dependencies

- cabal-install (version at least 3.2)
- ghc (version at least 8.10)
- make (optional for make command, version at least 4.3)

## Building

The program contains a [Makefile](Makefile) configured to build the program independently on the platform.

It is run by the common command:

```sh
make build
```

Alternatively, it could be built by using the cabal directly:

```sh
cabal new-build all
```

## Usage

The easiest way to run the compiler is to use the [run.sh](run.sh) script (may require `chmod`):

```sh
./run.sh <arguments>
```

Or it can be run by using cabal:

```sh
cabal new-run CHM-main <arguments>
```

For more information on the possible options and syntax run with an argument `--help`:

```sh
./run.sh --help
```
