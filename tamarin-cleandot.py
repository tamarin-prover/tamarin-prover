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
from string import digits, whitespace
from pyparsing import \
        Literal, Word, ZeroOrMore, OneOrMore, oneOf, Group, Dict, Optional, \
        printables, alphanums, nums, ParseException, restOfLine, Forward, delimitedList, \
        nestedExpr, Keyword, Combine
import pprint


CCOUNT = 0
CLUSTERCOLOR1 = [140,220,255]
CLUSTERCOLOR2 = [220,180,255]
labelbnf = None

class rules(object):

    def __init__(self,D):
        # The init is a dict of lists. We can later use this to reinsert data.
        self.data = D
        self.abbreviations = []
        self.dirty = True

    def checkDirty(self):
        if self.dirty:
            l = []
            for k in self.data.keys():
                l += subsequences(self.data[k])
            self.subs = l
            self.renders = map(render,self.subs)
            self.dirty = False

    def getTerms(self):
        self.checkDirty()
        return self.subs

    def exists(self,string):
        for (ta,sa) in self.abbreviations:
            if string == sa:
                return True
        self.checkDirty()
        return (string in self.renders)

    def size(self,term):
        return len(render(term))

    def ignore(self,term):
        # returns true iff TERM should not be considered for abbreviations
        if isIgnored(term):
            return True
        if isTermlist(term):
            return False
        else:
            return True
        

    def subst(self,l,tt,string):
        if render(l) == tt:
            return string
        else:
            if isinstance(l,list):
                nl = []
                for x in l:
                    nl.append(self.subst(x,tt,string))
                return nl
            else:
                return l

    def abbreviate(self,term,string):
        tt = render(term)

        print "Abbreviating '%s' by '%s'" % (tt,string)

        # Replace data
        for k in self.data.keys():
            self.data[k] = self.subst(self.data[k],tt,string)
        self.dirty = True
        
        # Replace existing abbreviations
        for i in range(0,len(self.abbreviations)):
            (ta,sa) = self.abbreviations[i]
            self.abbreviations[i] = (self.subst(ta,tt,string),sa)
        
        # abbreviate TERM by string
        self.abbreviations.append((term,string))

        

    def prefix(self,term):
        # Returns a string: if we want to abbreviate TERM, what would be an appropriate prefix string?
        allowed = alphanums + "_-!$~"
        i = 0
        tt = render(term)
        prefix = ""
        while i < len(tt) and len(prefix) < 3:
            if tt[i] in allowed:
                if tt[i] in alphanums:
                    prefix += tt[i]
                i += 1
            else:
                break

        if len(prefix) == 0:
            if tt[0] in "({[<" or tt.startswith("\<"):
                prefix = "S"
            else:
                prefix = "M"
        return prefix.upper()

    def isDone(self):
        # Returns true if we are done. No need to call this, usually.
        return False

    def summary(self):
        return (self.data, self.abbreviations)


def abbreviate(O):
    """
    Abbreviate some terms

    The input object should provide the following methods:

    getTerms()
        return a list of term-like objects of unspecified type, say TERM

    exists(string)
        returns true iff this string already occurs in the term list (renderings). Needed to compute a unique new string.

    size(TERM)
        returns a size indicator for the term

    ignore(TERM)
        returns true iff TERM should not be considered for abbreviations

    abbreviate(TERM,string)
        abbreviate TERM by string

    prefix(TERM)
        Returns a string: if we want to abbreviate TERM, what would be an appropriate prefix string?

    isDone()
        Returns true if we are done. No need to call this, usually.

    """

    def mightAbbreviate(O,t,occ):
        # Returns a "benefit" larger than 0, or -1 if no need to abbreviate
        if O.ignore(t):
            return -1
        if O.size(t) < 7:
            return -1
        if O.size(t) < 20 and occ == 1:
            return -1
        return ((2+occ) ** 2) * O.size(t)

    count = 0
    while True:
        # Termination conditions
        if O.isDone():
            return

        seen = []
        bestterm = None
        bestgain = -1
        terms = O.getTerms()
        for i in range(0,len(terms)):
            t = terms[i]
            if not (O.ignore(t) or t in seen):
                seen.append(t)
                occ = 1
                for j in range(i+1,len(terms)):
                    if terms[j] == t:
                        occ += 1
                print "Occurrences:",occ,render(t)
                gain = mightAbbreviate(O,t,occ)
                if gain > bestgain:
                    bestterm = t
                    bestgain = gain

        if bestgain <= 0:
            return 

        # We could do a complex thing here relating bestgain to count, but we keep it simple for now
        if count >= 7:
            return

        # Now come up with a name for it
        nr = 0
        prefix = O.prefix(bestterm)
        while True:
            nr += 1
            short = "%s%i" % (prefix,nr)
            if not O.exists(short):
                break

        # Propagate
        O.abbreviate(bestterm,short)
        count += 1

        # Iterate



def label_BNF():

    global labelbnf
    
    if not labelbnf:
        
        # punctuation
        lparen = Literal("(")
        rparen = Literal(")")
        lbrack = Literal("[")
        rbrack = Literal("]")
        lcbrack = Literal("{")
        rcbrack = Literal("}")
        bang = Literal("!")
        rvsep = Literal("|")
        equals = Literal("=")
        semi   = Literal(";")
        colon  = Literal(":")
        sharp  = Literal("#")
        tilde  = Literal("~")
        akrol  = Literal("@")
        dollar = Literal("$")
        comma = Literal(",")
        nbsp  = Literal("&nbsp;")
        dotnewline  = Literal("\l")

        quote = "'"

        def exceptfor(x):
            return "".join( [ c for c in printables if c not in x ] ) + " \t"

        CONST = Combine(Literal(quote) + Word(exceptfor(quote)) + Literal(quote))

        BASICID = Combine(Word( alphanums + "_-") + Optional(Literal(".") + Word(nums)))
        senc = Literal("senc")
        aenc = Literal("aenc")
        KEYWORD = senc | aenc
        ID = ~KEYWORD + Combine(Optional(dollar | tilde | sharp) + BASICID)
        TIME = Group(akrol + Combine(sharp + BASICID))

        TERM = Forward()
        TERMLIST = TERM + ZeroOrMore(comma + TERM)
        TUPLE1 = Group(Literal('<') + TERMLIST + Literal('>'))
        TUPLE2 = Group(Literal('\<') + TERMLIST + Literal('\>'))
        TUPLE3 = Group(Literal('(') + TERMLIST + Literal(')'))
        TUPLE = TUPLE1 | TUPLE2 | TUPLE3
        ARG = Literal('(') + TERMLIST + Literal(')')
        FUNC = Group(ID + Optional(ARG))
        ENC = Group((senc | aenc) + ARG)
        TERM << (ENC | FUNC | TUPLE | CONST )

        TPAREN = lparen + TERMLIST + rparen
        TBRACK = lbrack + Optional(TERMLIST) + rbrack
        FACT = Group(Combine(Optional(bang) + ID) + Optional(TPAREN | TBRACK) + Optional(TIME))

        PORT = Combine(Literal("<") + BASICID + Literal(">"))
        SINGLE = Optional(sharp + ID + colon) + (FACT | TERM)
        FIELDID = Group(Optional(PORT) + SINGLE)

        LABEL = Forward()
        FIELD = (lcbrack + LABEL + rcbrack) | FIELDID
        LABEL << FIELD + ZeroOrMore(rvsep + FIELD)

        labelbnf = Optional(Literal('"')) + LABEL + Optional(Literal('"'))
        
        labelbnf.ignore( nbsp  )
        labelbnf.ignore( dotnewline  )
        
    return labelbnf


def render(tokens):
    try:
        s = ""
        for x in tokens:
            s += render(x)
    except:
        s = str(tokens)
        pass
    return s

def subsequences(tokens):
    """
    Returns a list of lists (subsequences) of the tokens

    Note that we remove redundant sublists, i.e., for [[a]] we return [a], and NOT ([a] and [[a]]).
    This helps counter some overzealous grouping.
    """
    if not isinstance(tokens,list):
        return []
    if len(tokens) == 1:
        if isinstance(tokens[0],list):
            # Skip redundant subsequencing
            return subsequences(tokens[0])
    s = []
    for x in tokens:
        s += subsequences(x)
    return s + [tokens]

def matchEnds(L,first,last):
    try:
        if L[0] == first and L[-1] == last:
            return True
    except:
        pass
    return False

def isPort(tokens):
    if isinstance(tokens,str):
        if matchEnds(tokens,"<",">"):
            return True
    return False

def ports(tokens):
    res = []
    for l in subsequences(tokens):
        if isPort(l[0]):
            res.append(l[0])
    return res

def isTermlist(L):
    """
    Check if something is possibly a term (or a fact even)
    """
    if isPort(L[0]):
        # Ignoring port spec + following
        return False
    if matchEnds(L,"{","}"):
        # Record
        return False
    if L[0] == "@":
        return False
    return True

def isIgnored(L):
    if len(L) == 1:
        # Too small, will not abbreviate
        return True
    if isPort(L[0]):
        # Ignoring port spec + following
        return True

    if matchEnds(L,'"','"'):
        # Outer
        return True

    if matchEnds(L,"{","}"):
        # Record
        return True
    return False

def subterms(tokens):
    """
    Extract all subterms that may be candidates for abbreviations
    """
    subterms = []
    L = subsequences(tokens)
    for l in L:
        if isTermlist(l):
            subterms.append(l)
    return subterms
    

def parseLabel( strng ):

    print "*" * 40
    print "Original: ", strng

    pp = pprint.PrettyPrinter(2)
    try:
        bnf = label_BNF()
        tokens = bnf.parseString( strng ).asList()
        #pp.pprint(tokens)
        ###pp.pprint( tokens.asList() )

    except ParseException, err:
        print err.line
        print " "*(err.column-1) + "^"
        print err
    
    print "New     : ", render(tokens)
    print "Ports   : ", ports(tokens)
    print "*" * 40
    return tokens


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
        if s[i] == "\\":
            # Simply skip the escaped characters
            i += 2
        elif s[i] == "{":
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
    Get node prefix up to digit or None from a Node
    """

    fullname = getRuleName(N)
    if fullname == None:
        return None

    #print "@@@%s@@@" % fullname

    for i in range(0,len(fullname)):
        if fullname[i] in digits:
            # Prefix must be at least 1 character
            if i >= 1:
                return fullname[:i]
            else:
                return None
    return None


def incomingEdges(G,N):
    """
    Collect incoming edges of node N
    """
    l = G.get_edge_list()
    res = []
    n = N.get_name()
    for e in l:
        if e.get_destination() == n:
            res.append(e)
    return res


def outgoingEdges(G,N):
    """
    Collect outgoing edges of node N
    """
    l = G.get_edge_list()
    res = []
    n = N.get_name()
    for e in l:
        if e.get_source() == n:
            res.append(e)
    return res


def areConnected(G,src,dst):
    """
    src and dst are node names
    return True if they are connected by an edge
    """
    l = G.get_edge_list()
    for e in l:
        if e.get_source() == src and e.get_destination() == dst:
            return True
    return False



def del_node(G, name, index=None):
        """Delete a node from the graph.
       
        Given a node's name all node(s) with that same name
        will be deleted if 'index' is not specified or set
        to None.
        If there are several nodes with that same name and
        'index' is given, only the node in that position
        will be deleted.
       
        'index' should be an integer specifying the position
        of the node to delete. If index is larger than the
        number of nodes with that name, no action is taken.
       
        If nodes are deleted it returns True. If no action
        is taken it returns False.
        """
   
        if isinstance(name, Node):
            name = name.get_name()
       
        if G.obj_dict['nodes'].has_key(name):
       
            if index is not None and index < len(G.obj_dict['nodes'][name]):
                del G.obj_dict['nodes'][name][index]
                return True
            else:
                del G.obj_dict['nodes'][name]
                return True
       
        return False
                       
def del_edge(G, src_or_list, dst=None, index=None):
        """Delete an edge from the graph.
       
        Given an edge's (source, destination) node names all
        matching edges(s) will be deleted if 'index' is not
        specified or set to None.
        If there are several matching edges and 'index' is
        given, only the edge in that position will be deleted.
       
        'index' should be an integer specifying the position
        of the edge to delete. If index is larger than the
        number of matching edges, no action is taken.
       
        If edges are deleted it returns True. If no action
        is taken it returns False.
        """

        if isinstance( src_or_list, (list, tuple)):
            if dst is not None and isinstance(dst, (int, long)):
                index = dst
            src, dst = src_or_list
        else:
            src, dst = src_or_list, dst
   
        if isinstance(src, Node):
            src = src.get_name()

        if isinstance(dst, Node):
            dst = dst.get_name()
       
        if G.obj_dict['edges'].has_key( (src, dst) ):
       
            if index is not None and index < len(G.obj_dict['edges'][(src, dst)]):
                del G.obj_dict['edges'][(src, dst)][index]
                return True
            else:
                del G.obj_dict['edges'][(src, dst)]
                return True
       
        return False
        


def removeNode(G,N):
    """
    Remove node N from the graph.
    Keep edge structure intact:
    
    We hook up incoming and outgoing edges, replacing them by the product.

    (flow left-to-right)
    a   d      a    a
     \ /        \    \
      c    ==>   d    e
     / \        /    /
    b   e      b    b

    Of course, we should only add edges that don't exist yet.
    """

    # Collect
    incoming = incomingEdges(G,N)
    outgoing = outgoingEdges(G,N)

    # We first create new things before we remove old ones
    for Ein in incoming:
        src = Ein.get_source()
        for Eout in outgoing:
            dst = Eout.get_destination()
            if not areConnected(G,src,dst):
                G.add_edge(Edge(src,dst))

    # Remove old edges
    for edge in incoming + outgoing:
        del_edge(G,edge.get_source(),edge.get_destination())
    
    # Remove node
    del_node(G,N)

    return G



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


def isDerivationNode(G,N):
    """
    Returns True iff the node N seems to be a derivation node.
    """
    sh = N.get("shape")
    if sh != None:
        if "record" in sh:
            # Only record nodes are 'regular' rule instances
            return False
    return True

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


def isRedundantDerivation(G,N):
    """
    See collapseDerivations for the purpose of this check
    """
    if not isDerivationNode(G,N):
        return False
    incoming = incomingEdges(G,N)
    outgoing = outgoingEdges(G,N)
    if len(incoming) == 0 or len(outgoing) == 0:
        return False

    # TODO: check for non-derivation nodes "inbetween"
    
    return True


def collapseDerivations(G):
    """
    Collapse multiple term derivations into summary nodes.

    Derivation nodes are ellipses and not boxes or records, so they can be identified.

    If we have two derivation nodes connected by an edge, and no non-derivation node "inbetween" them, we can collapse them.
    This is similar to what Scyther does.

    Some side cases:

    - Derivation node with only outgoing edges.
      * We keep it
    - Derivation node with only incoming edges.
      * We keep it.
      
    Essentially we want to "summarize" all other derivation edges into single ones.

    """

    while True:
        # Try to find a derivation node that fits the bill
        found = False
        for N in G.get_node_list():
            if isRedundantDerivation(G,N):
                removeNode(G,N)
                found = True
                break
        if not found:
            return G






def showClusters(G):
    """
    Make clusters visible on the basis of rule prefixes.

    This function determines what should be clustered, clusters them, and provides them with a cluster background color. This makes some graphs significantly easier to grasp.

    TODO: For consistency, we could also simply compute the color off of the concrete prefix. Maybe easier during a proof (no color switches!)

    TODO: Facts connected between in-cluster edges can simply be emptied. Basis: edge between two nodes within a single cluster needs to annotation. Nodes/ports from which all edges are not needed can be collapsed. In other words: inspect all incoming and outgoing edges. If there is none from outside the cluster, then collapse the node:port. Nodes in clusters are records anyway.
    """

    (prefixes, clusters) = findClusters(G)
    prefixes.sort()

    CL = makeColorList(len(prefixes),CLUSTERCOLOR1,CLUSTERCOLOR2)

    for (pf,cl) in clusters:
        i = prefixes.index(pf)
        CLwhite = makeColorList(3,CL[i],[255,255,255])
        createCluster(G,cl,prefix=pf,color=hexColor(CLwhite[1]),fillcolor=hexColor(CL[i]))

    return G


def abbreviateGraph(G):
    """
    Add abbreviatios to a graph

    Currently we assume only nodes have labels
    """
    NL = G.get_node_list()
    D = {}
    for N in NL:
        nn = N.get_name()
        label = N.get_label()
        if label != None:
            D[nn] = parseLabel(label)

    R = rules(D)
    abbreviate(R)
    (D,S) = R.summary()

    for N in NL:
        nn = N.get_name()
        if nn in D.keys():
            N.set_label(render(D[nn]))

    l = "Abbreviations\l\l"
    for (x,y) in S:
        l += "%s = %s\l" % (y,render(x))

    N = Node()
    N.set_label("\"%s\"" % (l))
    N.set_shape("box")

    S = Subgraph()
    S.set("rank","sink")
    S.set("style","invis")
    S.add_node(N)
    G.add_subgraph(S)

    return G


def improveGraph(G):
    """
    Improve a graph
    """

    G = showClusters(G)
    G = collapseDerivations(G)
    G = abbreviateGraph(G)
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


