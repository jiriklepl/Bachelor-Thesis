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

.precompiled.c: build
	cabal new-run -v0 CHM-instantiate > .precompiled.c

.assembly.S: .precompiled.c
	gcc -S -O0 -o .assembly.S .precompiled.c

.main: .assembly.S
	gcc -o .main .assembly.S
