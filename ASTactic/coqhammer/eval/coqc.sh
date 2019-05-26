#!/bin/bash

rm -f "$2" > /dev/null 2>&1
while ! timeout 1200 coqc "$1" >> "$2" 2>&1 ; do
    echo "repeat" >> "$2"
done
