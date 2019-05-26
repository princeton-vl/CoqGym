#!/bin/bash

DIR=`dirname "$0"`

for f in `find . -name "*.v" -print`; do
    cp "$f" "$f.bak"
    cat "$f.bak" | "$DIR/rmcomments" > "$f"
done
"$DIR/coqnames"
