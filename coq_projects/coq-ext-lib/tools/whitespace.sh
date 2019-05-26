#!/bin/sh

for x in $*
do
    sed -i 's/[ \t]*$//' $x
done