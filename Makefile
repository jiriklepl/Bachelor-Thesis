.PHONY: build clean run

build:
	cabal new-build all --haddock-internal

clean:
	cabal new-clean

run:
	cabal new-run CHM-instantiate --haddock-internal

compile:
	cabal new-run -v0 CHM-instantiate --haddock-internal > .precompiled.c
	gcc -S -O0 -o .assembly.S .precompiled.c
	gcc -c -o .main .assembly.S
