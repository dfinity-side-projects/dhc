# Dfinity Haskell Compiler

image:https://jenkins.london.dfinity.build/job/dhc/badge/icon[link="https://jenkins.london.dfinity.build/job/dhc/"]

## Summary
DHC is a Haskell compiler that produces WebAssembly.

It accepts only a tiny subset of the language.
There is almost no syntax sugar.

Lambdas compile incorrectly. They should be manually lifted instead.

There is no support for the `S` (strings), `Call` and `Qual` language features
declared in `DHC.hs`, which are used by other Dfinity projects.

## Live demo
https://dhc.dfinity.org/[https://dhc.dfinity.org/]

## Installation / Dependencies
TBD

## Usage / Examples
TBD

## Caveats
TBD

## License

**(C) 2017 DFINITY STIFTUNG** (http://dfinity.network)

All code and designs are open sourced under GPL V3.

![dfinity logo](https://user-images.githubusercontent.com/6457089/32753794-10f4cbc2-c883-11e7-8dcf-ff8088b38f9f.png)
