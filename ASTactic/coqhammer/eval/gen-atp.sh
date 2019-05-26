#!/bin/bash

echo "gen-atp" > coqhammer.opt
rm -rf logs/atp/
rm -rf atp/problems
rm gen-atp.log
make -k -j "$1" atp 2>&1 | tee gen-atp.log
mv gen-atp.log gen-atp.log.bak
cat gen-atp.log.bak | grep Error > gen-atp.log
rm gen-atp.log.bak
if [ -n "$2" ]; then
    echo "" | mail -s "ATP problem generation finished" "$2"
fi
