#!/bin/bash

OPAM_SWITCH="4.07.1+flambda"
COQ_DEPENDENCIES="coq"
COQ_ROOT=$(pwd)/coq

SERAPI_DEPENDENCIES="dune cmdliner ppx_sexp_conv ppx_deriving sexplib ppx_import"

echo "Installing Coq.."
opam switch $OPAM_SWITCH && eval $(opam env)
opam install --yes $COQ_DEPENDENCIES
cd coq
./configure -local -flambda-opts '-O3 -unbox-closures' && make
cd ..
export COQBIN=$COQ_ROOT/bin/
export PATH=$COQBIN:$PATH

echo "Installing SerAPI.."
opam install --yes $SERAPI_DEPENDENCIES
cd coq-serapi
make SERAPI_COQ_HOME=$COQ_ROOT
dune install
cd ..

echo "Installing CoqHammer.."
cd ASTactic/coqhammer
make
make install
cd ../..

echo "Coq, SerAPI and CoqHammer installed."
