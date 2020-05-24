.PHONY: build clean run

build:
	cabal build all --haddock-internal

clean:
	cabal clean

run:
	cabal run CHM-instantiate --haddock-internal

compile:
	cabal run -v0 CHM-instantiate --haddock-internal | gcc -o main -xc -
