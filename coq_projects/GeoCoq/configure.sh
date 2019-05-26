#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" | grep -v Sandbox >> Make
coq_makefile -f Make -o Makefile
