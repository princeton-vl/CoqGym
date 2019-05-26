#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" | grep POF >> Make
coq_makefile -f Make -o Makefile
