#!/usr/bin/env bash
./vardlog.native -dbpath /tmp/vard-log-$2 -me $1 -port $2 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002
