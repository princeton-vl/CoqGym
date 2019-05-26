#!/usr/bin/env bash

if ! [ -x ./TPCMain.d.byte ]
then
    echo 'TPCMain.d.byte not found!'
    echo 'Run `make TPCMain.d.byte` first.'
    exit 1
fi

(./TPCMain.d.byte -me 1 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >particpant1.log

(./TPCMain.d.byte -me 2 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >particpant2.log

(./TPCMain.d.byte -me 3 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >particpant3.log

./TPCMain.d.byte -me 0 -mode coordinator 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 | tee coordinator.log
