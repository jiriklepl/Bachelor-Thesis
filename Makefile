.PHONY: build clean run

build:
	cabal build all --haddock-internal

clean:
	cabal clean

run: build
	cabal run CHM-instantiate --haddock-internal
