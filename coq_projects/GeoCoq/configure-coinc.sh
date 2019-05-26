#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" | grep "Tactics/Coinc/" >> Make
find . -name "*.v" | grep Utils >> Make
coq_makefile -f Make -o Makefile
