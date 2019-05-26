#!/bin/bash

rm -f problems || rm -rf problems
cd tests
make clean
cd ..
cp -r tests problems
echo "check" > coqhammer.opt
cd tests
make -k -j "$1"
cd ..
./gen-atp.sh "$1"
