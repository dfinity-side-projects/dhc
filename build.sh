#!/bin/sh

mkdir -p build
stack build
cp $(stack path --local-install-root)/bin/dhc-js.jsexe/*.js build
echo "(function(global) {" > build/index.js
cat build/{rts,lib,out}.js util/wrapper.js >> build/index.js
echo "})(exports);" >> build/index.js
