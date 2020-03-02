.PHONY: build clean run

build:
	cabal build all

clean:
	cabal clean

run:
	cabal run CHM-instantiate
