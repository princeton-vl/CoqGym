#!/usr/bin/env bash

set -ev

export MODE=$1
export OPAMBUILDTEST=$2

eval $(opam config env)

opam update

case ${MODE} in
  cheerios-runtime)
    opam pin add cheerios-runtime . --yes --verbose
    ;;
  *)
    opam pin add cheerios . --yes --verbose
    ;;
esac
