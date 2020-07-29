.PHONY: build clean haddock

build:
	cabal new-build all

clean:
	cabal new-clean

haddock:
	cabal new-haddock all --internal
