build:
	stack build --flag leadbeater:liquidhaskell

.phony: build

test:
	stack exec -- liquid -isrc test/*.hs
	stack test --flag leadbeater:liquidhaskell

.phony: test