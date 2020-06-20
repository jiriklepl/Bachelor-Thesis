.PHONY: build clean run haddock compile

build:
	cabal new-build all

clean:
	cabal new-clean

run:
	cabal new-run CHM-instantiate

haddock:
	cabal new-haddock all --internal

compile: .main

opt_compile: .opt_main

.precompiled.c: build
	cabal new-run -v0 CHM-instantiate > .precompiled.c

.assembly.S: .precompiled.c
	gcc -S -O0 -o .assembly.S .precompiled.c

.opt_assembly.S: .precompiled.c
	gcc -S -O2 -o .opt_assembly.S .precompiled.c

.main: .assembly.S
	gcc -O0 -o .main .assembly.S

.opt_main: .opt_assembly.S
	gcc -O2 -o .main .opt_assembly.S
