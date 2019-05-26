#!/bin/bash

mkdir i
for d in problems/*
do
    echo "***************"
    echo $d
    rm -f i/f
    ln -s ../$d i/f
    make -k -j "$1" eprover vampire z3 cvc4
    p=`basename $d`
    mv o/eprover o/eprover-$p
    mv o/vampire o/vampire-$p
    mv o/z3 o/z3-$p
    mv o/cvc4 o/cvc4-$p
    if [ -n "$2" ]; then
        echo "" | mail -s "provers $p finished" "$2"
    fi
done
if [ -n "$2" ]; then
    echo "" | mail -s "Provers finished" "$2"
fi
