all:
	mkdir -p build
	alex src/Lex.x -o build/Lex.hs
	happy src/Synt.y -o build/Synt.hs
	ghc build/Lex.hs build/Synt.hs src/Main.hs src/Grammar.hs -o parser

run:
	./parser

zip:
		zip second.zip src/Lex.x src/Synt.y src/Main.hs src/Grammar.hs Makefile
