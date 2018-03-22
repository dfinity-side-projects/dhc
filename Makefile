.PHONY: all test clean
all: dhcdemo.js dhcdemo.html
dhcdemo.js: *.hs dhcdemo.lhs; hastec -Wall dhcdemo.lhs
dhcdemo.html: dhcdemo.lhs; asciidoc dhcdemo.lhs
test:; ghc -O2 -Wall test/Main.hs && test/Main
clean:; rm -rf *.hi; rm -rf *.jsmod; rm -rf *.o
