#!/bin/bash

OCAML_VER=4.06.1

# build 32 bits parts
opam switch $OCAML_VER+32bit
eval `opam config env`

# Change to your jscoq location
export SERAPI_COQ_HOME=/home/egallego/research/jscoq/coq-external/coq-v8.8+32bit/

make js/sertop_js.js
make js-dist

