#!/bin/bash

echo "check" > coqhammer.opt
rm -rf logs/check/
rm check.log
make -k -j "$1" check 2>&1 | tee check.log
mv check.log check.log.bak
cat check.log.bak | grep Error > check.log
rm check.log.bak
