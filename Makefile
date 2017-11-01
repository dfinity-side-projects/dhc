all: dhcdemo.js dhcdemo.html
dhcdemo.js: dhcdemo.lhs; hastec --full-unicode -Wall dhcdemo.lhs
dhcdemo.html: dhcdemo.lhs; asciidoc dhcdemo.lhs
