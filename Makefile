build:
	stack build --flag leadbeater:liquidhaskell

.PHONY: build

test:
	stack exec -- liquid -isrc test/*.hs
	stack test --flag leadbeater:liquidhaskell

.PHONY: test

clean:
	stack clean

.PHONY: clean
