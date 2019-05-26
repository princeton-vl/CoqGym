#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" | grep Axioms >> Make
find . -name "*.v" | grep Definitions >> Make
find . -name "*.v" | grep finish >> Make
coq_makefile -f Make -o Makefile
