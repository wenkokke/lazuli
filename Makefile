build:
	stack build --flag lazuli:liquidhaskell

.PHONY: build

test:
	stack exec -- liquid -isrc models/*.hs
	stack test --flag lazuli:liquidhaskell

.PHONY: test

clean:
	stack clean

.PHONY: clean
