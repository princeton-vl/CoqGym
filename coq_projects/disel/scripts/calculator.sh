#!/usr/bin/env bash

if ! [ -x ./CalculatorMain.d.byte ]
then
    echo 'CalculatorMain.d.byte not found!'
    echo 'Run `make CalculatorMain.d.byte` first.'
    exit 1
fi

(./CalculatorMain.d.byte -me 1 -mode server 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 &) >server1.log 2>&1

(./CalculatorMain.d.byte -me 3 -mode server 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 &) >server3.log 2>&1

./CalculatorMain.d.byte -me 2 -mode client -server 3 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 | tee client.log
