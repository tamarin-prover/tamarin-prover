#!/bin/sh

/usr/bin/dot -Tpng -o test-original.png test.dot
./tamarin-cleandot.py -Tpng -o test-improved.png test.dot
