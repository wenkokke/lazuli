build:
	stack build --flag leadbeater:liquidhaskell

test:
	stack exec -- liquid -isrc test/*.hs
	stack test --flag leadbeater:liquidhaskell