#!/bin/bash

./gen-atp.sh $1 $2
cd atp
./run-provers.sh $1 $2
cd ..
./run-reconstr.sh $1 $2
./gen-stats.sh
if [ -n "$2" ]; then
    echo "" | mail -s "Evaluation finished" "$2"
fi
