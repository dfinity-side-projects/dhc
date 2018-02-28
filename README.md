# Dfinity Haskell Compiler

[![Build Status](https://jenkins.london.dfinity.build/job/dhc/badge/icon)](https://jenkins.london.dfinity.build/job/dhc/)

## Summary
DHC is a Haskell compiler that produces WebAssembly.

It accepts only a tiny subset of the language.

## Live demo

https://dhc.dfinity.org

## Installation / Dependencies
    stack setup
    ./build.sh

## Usage / Examples
```javascript
const dhc = require('./build')

const output = dhc.compileHsToWasm('main = putStr "Hello"')
// [ 0, 97, 115, 109, ... ]

const err = dhc.compileHsToWasm('syntax error')
// '(line 1, column 13):\nunexpected end of input\nexpecting " ", "\\r\\n", "--" or end of input\nexpected ='
```

## Caveats
TBD

## License

**(C) 2018 DFINITY STIFTUNG** (http://dfinity.org)

All code and designs are open sourced under GPL V3.

![dfinity logo](https://user-images.githubusercontent.com/6457089/32753794-10f4cbc2-c883-11e7-8dcf-ff8088b38f9f.png)
