#!/usr/bin/env bash

set -ev

export DOWNSTREAM=$1

eval $(opam config env)

opam update

opam pin add InfSeqExt . --yes --verbose

case ${DOWNSTREAM} in
verdi)
  opam install verdi --yes --verbose
  ;;
esac
