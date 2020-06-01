.PHONY: build clean run haddock compile

build:
	cabal new-build all

clean:
	cabal new-clean

run:
	cabal new-run CHM-instantiate

haddock:
	cabal new-haddock all --internal

compile: build
	cabal new-run -v0 CHM-instantiate > .precompiled.c
	gcc -S -O0 -o .assembly.S .precompiled.c
	gcc -c -o .main .assembly.S
