#!/bin/sh

SRC=test.dot
#SRC="test-big.dot"

/usr/bin/dot -Tpng -o test-original.png $SRC
./tamarin-cleandot.py -Tpng -o test-improved.png $SRC
