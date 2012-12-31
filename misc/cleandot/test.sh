#!/bin/sh

/usr/bin/dot -Tpng -o test.png test.dot
./tamarin-cleandot.py -Tpng -o test2.png test.dot
