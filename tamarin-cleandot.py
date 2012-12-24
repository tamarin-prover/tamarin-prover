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


CCOUNT = 0
CLUSTERCOLOR1 = [140,220,255]
CLUSTERCOLOR2 = [220,180,255]

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


def getSubfield(s,location):
    """
    Consider s as an html-formatted record type string.
    Use brackets etc. to locate the required subfield.
    """

    spec = "{}|"
    horizontal = True
    depth = 0
    loc = []
    count = 1
    i = 0
    while i < len(s):
        if s[i] == "{":
            horizontal = not(horizontal)
            loc.append(count)
            count = 1
            depth += 1
            i += 1
        elif s[i] == "}":
            horizontal = not(horizontal)
            depth -= 1
            count = loc.pop(-1)
            i += 1
        elif s[i] == "|":
            count += 1
            i += 1
        else:
            j = i
            while j < len(s):
                if s[j] in spec:
                    break
                j += 1

            if location == loc:
                return s[i:j]

            i = j

    return None


def getRuleName(N):
    """
    Try to reconstruct the rule name or None.
    Tricky business.
    """
    sh = N.get("shape")
    if sh == None:
        return None
    if not ("record" in sh):
        return None

    label = N.get("label")
    ruleField = getSubfield(label,[1,2])

    try:
        i = ruleField.index(":")
        j = ruleField.index("[",i)

        return ruleField[i+1:j].strip()
    except:
        pass

    return None


def getPrefix(N):
    """
    Get node prefix up to digit or None
    """
    from string import digits

    fullname = getRuleName(N)
    if fullname == None:
        return None

    print "@@@%s@@@" % fullname

    for i in range(0,len(fullname)):
        if fullname[i] in digits:
            # Prefix must be at least 1 character
            if i >= 1:
                return fullname[:i]
            else:
                return None
    return None


def noPort(nn):
    """
    Strip port part of node name
    """
    i = nn.find(":")
    if i >= 0:
        nn = nn[:i]
    return nn


def findNode(G,nn):
    """
    Given a node name, get the node
    """
    for n in G.get_nodes():
        if n.get_name() == nn:
            return n

    return None

def findSomeConnected(G,NL,prefix=""):
    """
    Given a graph an a list of node names, find additional node names that were not in there yet.
    With additional prefix shared.
    """
    l = G.get_edges()
    new = []
    for edge in l:
        src = noPort(edge.get_source())
        dst = noPort(edge.get_destination())
        srcN = findNode(G,src)
        dstN = findNode(G,dst)
        srcR = getRuleName(srcN)
        dstR = getRuleName(dstN)
        if dstR != None and srcR != None:
            if dstR.startswith(prefix) and srcR.startswith(prefix):
                if src in NL:
                    if dst not in NL:
                        new.append(dst)
                if dst in NL:
                    if src not in NL:
                        new.append(src)
    return new

def findConnected(G,NL,prefix=""):
    """
    Iteratively find all connected
    """
    while True:
        D = findSomeConnected(G,NL,prefix=prefix)
        if len(D) == 0:
            return NL
        NL = NL + D

    return NL


def sanitizePrefix(s):
    """
    Prefixes tend to end in funny stuff. Get rid of it.
    """
    if len(s) == 0:
        return s

    while s[-1] in "-=+*_":
        s = s[:-1]
        if len(s) == 0:
            break

    return s

def makeNewWithPrefix(G,prefix=""):
    """
    Given a prefix, make a fresh unique cluster name for it
    """
    global CCOUNT

    CCOUNT += 1

    name =  "_CLUSTER_%s_%i" % (prefix,CCOUNT)
    label =  "%s (%i)" % (sanitizePrefix(prefix),CCOUNT)

    return (name,label)



def createCluster(G,NL,prefix="",color=None,fillcolor=None):
    """
    Given a list of node names, add a cluster for them.
    """
    (clustername,label) = makeNewWithPrefix(G,prefix=prefix)

    cluster = Cluster(clustername,label=label,style="filled",fillcolor=fillcolor,color=color)
    for nn in NL:
        n = findNode(G,nn)
        cluster.add_node(n)

    G.add_subgraph(cluster)


def findClusters(G):
    """
    Inspect a graph

    Return a list of clusters. Each cluster consists of a list of node names.
    """
    l = G.get_nodes()
    done = []
    prefixes = []
    clusters = []
    for n in l:
        if not n.get_name() in done:
            pf = getPrefix(n)
            if pf != None:

                if not pf in prefixes:
                    prefixes.append(pf)

                cl = findConnected(G,[n.get_name()],prefix=pf)

                # TODO: Sanity check: cl should have an empty intersection with done
                
                done = done + cl
                clusters.append((pf,cl))

    return (prefixes,clusters)


def hexColor(c):
    """
    Turn a RGB [0-255] triplet into a hex code
    """
    cstring = "#"
    for i in [0,1,2]:
        cstring += "%02X" % c[i]
    return cstring


def makeColorList(n,c1,c2):
    """
    Create a list of colors of length n, ranging from c1 to c2.
    c1 and c2 are RGB sequences where each component is in [0,255].
    """
    def colorrange(n, i, c):
        if n <= 1:
            return c1[c]
        else:
            d = (c2[c] - c1[c]) / float(n-1)
            return int(c1[c] + (i * d))

    l = []
    for i in range(0,n):
        cc  = []
        for c in [0,1,2]:
            cc.append(colorrange(n, i, c))
        l.append(cc)

    return l


def showClusters(G):
    """
    Make clusters visible on the basis of rule prefixes
    """

    (prefixes, clusters) = findClusters(G)

    CL = makeColorList(len(prefixes),CLUSTERCOLOR1,CLUSTERCOLOR2)

    for (pf,cl) in clusters:
        i = prefixes.index(pf)
        CLwhite = makeColorList(3,CL[i],[255,255,255])
        createCluster(G,cl,prefix=pf,color=hexColor(CLwhite[1]),fillcolor=hexColor(CL[i]))


def improveGraph(G):
    """
    Improve a graph
    """

    showClusters(G)
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


