#!/usr/bin/env python

"""
tamarin-cleandot.py

A postprocesser for Tamarin's dot output. The idea is to provide a drop-in
replacement for the dot program that takes care of the cleanup.

Its first aim is to provide more structure in the graphs by clustering possible
threads by using a heuristic. For now, this is done by searching for connected
nodes whose names share a prefix that is followed by a digit.

Future possibilites:
    - Abbreviations (as Scyther-compromise is doing now)
    - Node collapsing / simplification with a switch (but would need change in the Tamarin code to propagate)


December 2012, Cas Cremers


Usage:

    tamarin-cleandot.py file [options]

Where [options] is one of:

    -T imageformat
    -K dotmode
    -o imgfile

"""

from pydot import *
import os
import sys


def execDot(args):
    """
    Invoke the real dot program

    Note that args should be a list.
    """
    import subprocess

    cmd = "/usr/bin/dot"
    retcode = subprocess.call([cmd] + args)
    sys.exit(retcode)


def findArgs(infile=None):
    """
    Reconstruct args list from the program, but exclude the input file
    """
    args = []
    for x in sys.argv[1:]:
        if (infile == None) or (x != infile):
            args.append(x)

    return args


def findInputFile():
    fp = open("/tmp/tamarin-cleandot.log","a")
    fp.write("cleandot: Scanning for input file in: "+ str(sys.argv[1:])+ "\n")
    fp.close()

    # Currently, the Tamarin implementation is such that the filename is always the last argument.
    # This may change in the future, so a more robust parsing is maybe in order.
    infile = sys.argv[-1]

    return infile


def improveGraph(G):
    """
    Improve a graph
    """

    G.add_node(Node("TestingEdge"))
    return G


def newDot(infile):
    """
    Return a new filename with the improved graph.
    """
    from tempfile import mkstemp

    (fpint,outfile) = mkstemp(suffix=".dot")
    fp = os.fdopen(fpint,'w')
    
    G = graph_from_dot_file(infile)

    G = improveGraph(G)

    fp.write(G.to_string())

    fp.close()

    return outfile

def main():
    infile = findInputFile()
    nargs = findArgs(infile)
    outfile = newDot(infile)
    execDot(nargs + [outfile])


if __name__ == '__main__':
    main()


