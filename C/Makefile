HC=ghc
SOURCES=src/Main.hs src/Grammar.hs
GEN_SOURCES=src/Lex.x src/Synt.y
GENERATED=src/Lex.hs src/Synt.hs
PACKAGE=lab2.zip

.PHONY: pack all run clean test

all: solution

run: solution
	./solution

test: solution
	./test.sh

testall: solution
	./test.sh "ALL" > log.txt

clean:
	rm -rf src/*.o src/*.hi
	rm -rf $(GENERATED)
	rm -f solution

solution: $(GENERATED) $(SOURCES)
	$(HC) -O2 -XBangPatterns -i./src -tmpdir . ./src/Main.hs -o solution

$(GENERATED): $(GEN_SOURCES) $(SOURCES)
	alex src/Lex.x -o src/Lex.hs
	happy src/Synt.y -o src/Synt.hs

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src
