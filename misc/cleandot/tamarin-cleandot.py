#!/usr/bin/env python

"""
tamarin-cleandot.py

A postprocesser for Tamarin's dot output. The idea is to provide a drop-in
replacement for the dot program that takes care of the cleanup.

Its first aim is to provide more structure in the graphs by clustering possible
threads by using a heuristic. For now, this is done by searching for connected
nodes whose names share a prefix that is followed by a digit.

The comments in the dot file are used by Tamarin to guide tamarin-cleandot. In
particular, this is how the GUI switches are propagated: they end up in the
global PARAMETERS dict:

- simplification : [0..3]
- abbreviate : True/False

E.g.:
// simplification: X
// abbreviate: True

To do:
    The parameters now still include the static set of rules names. These
    should be used to determine a nice colour distribution.

December 2012 -- January 2013
Cas Cremers


Usage:

    tamarin-cleandot.py [options] file

Where [options] is one of:

    -T imageformat
    -K dotmode
    -o imgfile

If [options] contains '-V' or '--version', the input is handled directly by graphviz.


***********

Short-term wish list:

- Work on 'hiding' in-cluster connecting state facts, or collapse multiple such nodes into a single record.

- If Tamarin can output the rule names in the dotfile's comments, we can do a nicer color distribution.

"""

if __name__ == '__main__':
    import tamarincleandotlib

    tamarincleandotlib.main()

