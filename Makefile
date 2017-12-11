.PHONY: all test clean
all: dhcdemo.js dhcdemo.html
dhcdemo.js: Asm.hs DHC.hs dhcdemo.lhs; hastec --full-unicode -Wall dhcdemo.lhs
dhcdemo.html: dhcdemo.lhs; asciidoc dhcdemo.lhs
test:; ghc -Wall test/Main.hs && test/Main
clean:; rm -rf *.hi; rm -rf *.jsmod; rm -rf *.o
