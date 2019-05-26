#!/usr/bin/env bash
./vardserialized.native -dbpath /tmp/vard-serialized-$2 -me $1 -port $2 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002
