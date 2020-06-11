#!/bin/bash
OPAM_SWITCH="4.07.1+flambda"
COQ_ROOT=$(pwd)/coq
DEPENDENCIES="dune=1.10.0 cmdliner=1.0.4 ppx_sexp_conv=v0.12.0 ppx_deriving=4.3 sexplib=v0.12.0 ppx_import=1.6.2 camlp5=7.08 coq=8.9.1"

echo "Installing Dependencies.."
opam switch $OPAM_SWITCH && eval $(opam env)
opam install --yes $DEPENDENCIES
echo "Dependencies installed"

echo "Installing Coq.."
cd coq
./configure -local -flambda-opts '-O3 -unbox-closures' && make
cd ..
export COQBIN=$COQ_ROOT/bin/
export PATH=$COQBIN:$PATH
echo "Coq installed"

echo "Installing SerAPI.."
cd coq-serapi
make SERAPI_COQ_HOME=$COQ_ROOT
dune install
cd ..
echo "SerAPI installed"

echo "Installing CoqHammer.."
cd ASTactic/coqhammer
make
make install
cd ../..
echo "CoqHammer installed"

