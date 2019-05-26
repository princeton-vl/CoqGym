#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" | grep OriginalProofs >> Make
find . -name "*.v" | grep euclid_to_tarski >> Make
coq_makefile -f Make -o Makefile
