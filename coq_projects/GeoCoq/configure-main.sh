#!/usr/bin/env sh
cp -f Make.in Make
find . -name "*.v" | grep -v "Tactics/Coinc/" | grep -v Axioms | grep -v OriginalProofs | grep -v Utils | grep -v Sandbox | grep -v finish | grep -v euclid_to_tarski | grep -v POF >> Make
coq_makefile -f Make -o Makefile
