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

import os
import sys
from string import digits, whitespace
from pydot import *
from pyparsing import \
        Literal, Word, ZeroOrMore, OneOrMore, oneOf, Group, Dict, Optional, \
        printables, alphas, alphanums, nums, ParseException, restOfLine, Forward, delimitedList, \
        nestedExpr, Keyword, Combine, replaceWith, StringEnd
import pprint


# Clusters
CCOUNT = 0                       # Cluster count (used for naming)
CLUSTERCOLOR1 = (0.5,0.6,0.83)   # HSL
CLUSTERCOLOR2 = (1.2,0.6,0.83)   # HSL

# Global variable to store the pyparsing BNF.
labelbnf = None

# Global variable for storing dictionary with special parameters
PARAMETERS = {}

# DEBUG mode
DEBUGMODE = True
DEBUGPARAMETERS = False


class rules(object):
    """
    Rules object class for abbreviations purposes.

    Objects from this class store all the labels from nodes in a dict.

    The object serves as an interface for the abbreviation function, but it is
    not so cleanly split as we would want.

    My initial idea was to have a "generic" abbreviation function that I could
    directly use in Scyther as well, but that's not done yet.
    """

    def __init__(self,D):
        # The init is a dict of lists. We can later use this to reinsert data.
        self.data = D
        self.abbreviations = []     # Will contain (bigterm,abbreviation) pairs
        self.prefixes = {}          # Will map prefixes to (firstabbreviation,count) tuples; its purpose is to determine later what was only used once.
        self.dirty = True

    def subst(self,l,tt,string):
        """
        Substitute a single string in the data type that we use.
        (which is the nested list structure coming out of pyparsing)
        """
        if render(l) == tt:
            if isinstance(l,list):
                return [string]
            else:
                return string
        else:
            if isinstance(l,list):
                nl = []
                for x in l:
                    nl.append(self.subst(x,tt,string))
                return nl
            else:
                return l

    def replaceAll(self,src,dst):
        """
        Replace src by dst throughout the object.

        Return 'firstUse' usage point (or None) in existing abbreviation sequence
        """
        # Replace data
        for k in self.data.keys():
            self.data[k] = self.subst(self.data[k],src,dst)
        
        # Replace existing abbreviations
        # compute firstUse as the first usage point
        firstUse = None
        for i in range(0,len(self.abbreviations)):
            (ta,sa) = self.abbreviations[i]
            tb = self.subst(ta,src,dst)
            if sa == src:
                sa = dst
            self.abbreviations[i] = (tb,sa)
            if ta != tb and firstUse == None:
                firstUse = i

        self.dirty = True
        return firstUse


    def simplifySinglePrefix(self,prefix):
        """
        Try to simplify the abbreviation starting with the prefix.

        Use case: we often generate "hash1" when only one hash occurs.  In such
        cases we would have wanted to abbreviate it just by "hash".
        """
        (firstab,count) = self.prefixes[prefix]
        if count == 1:
            #print "Trying to simplify %s to %s" % (firstab,prefix)
            if not self.exists(prefix):
                # The isolated prefix is available, so we can replace 'firstab' by 'prefix'
                self.replaceAll(firstab,prefix)
                return True

        return False


    def simplify(self):
        """
        Simplify single prefix occurrences, if possible, by removing the counter
        """
        deleted = []
        for prefix in self.prefixes.keys():
            if self.simplifySinglePrefix(prefix):
                deleted.append(prefix)

        for prefix in deleted:
            del self.prefixes[prefix]


    def checkDirty(self):
        """
        We only unfold subsequences and renders when needed.
        """
        if self.dirty:
            l = []
            for k in self.data.keys():
                l += subsequences(self.data[k])
            for (ta,sa) in self.abbreviations:
                l += subsequences(ta)
            self.subs = l
            self.renders = map(render,self.subs)    # Maybe replace by list comprehension
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

    def isIgnored(self,L):
        if len(L) <= 1:
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

        if "[" in render(L) and "]" in render(L):
            # Rule names 'Init[...]' are never abbreviated (but of course their inner parts might)
            return True

        for (ta,sa) in self.abbreviations:
            # Check existing abbreviations
            if ta == L:
                # Already abbreviated
                return True

        return False

    def ignore(self,term):
        # returns true iff TERM should not be considered for abbreviations
        if self.isIgnored(term):
            return True
        if isTermlist(term):
            return False
        else:
            return True
        

    def abbreviate(self,term,string,prefix):
        # abbreviate TERM by string based on prefix
        # Note that we might be abbreviating some subterm of an existing definition.
        # We therefore want to insert the new abbreviation at a suitable point:
        # before it is first used.
        
        tt = render(term)

        #print "Abbreviating '%s' to '%s'" % (tt,string)

        firstUse = self.replaceAll(tt,string)
        
        # insert the new abbreviation before firstUse
        if firstUse == None:
            firstUse = len(self.abbreviations)
        pre = self.abbreviations[:firstUse]
        post = self.abbreviations[firstUse:]
        self.abbreviations = pre + [(term,string)] + post

        if prefix in self.prefixes.keys():
            (firstab,count) = self.prefixes[prefix]
            self.prefixes[prefix] = (firstab,count+1)
        else:
            self.prefixes[prefix] = (string,1)


    def prefix(self,term):
        """
        Returns a non-empty string: if we want to abbreviate TERM, what would be an appropriate prefix string?
        """
        preflen = 3     # Desired prefix length
        
        # First check first bit
        allowed = alphanums + "_-!$~"
        i = 0
        tt = render(term)
        prefix = ""
        while i < len(tt) and len(prefix) < preflen:
            if tt[i] in allowed:
                if tt[i] in alphanums:
                    prefix += tt[i]
                i += 1
            else:
                break

        # Is there a lone digit left?
        lone_digit = None
        if len(tt) > 0:
            j = i
            while j < len(tt):
                if not tt[j] in allowed:
                    break
                j += 1
            j -= 1
            while j >= i:
                if tt[j] in nums:
                    break
                j -= 1
            if j > i:
                if not tt[j-1] in nums:
                    lone_digit = tt[j]
        # Then add the lone digit (or even overwrite)
        if lone_digit and len(prefix) > 0:
            if len(prefix) < preflen:
                prefix += lone_digit
            else:
                prefix = prefix[:-1] + lone_digit

        # Isolate special cases and default to simple conventions
        if len(prefix) == 0:
            if tt[0] == "[":
                prefix = "S"
            elif tt[0] == "(":
                prefix = "P"
            elif tt[0] == "<" or tt.startswith("\<"):
                prefix = "T"
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

    def niceName(prefix):
        # Now come up with a name for it
        #
        # If ends in a digit, then we want alphas
        if prefix[-1] in nums:
            for c in alphas.lower():
                short = "%s%s" % (prefix,c)
                if not O.exists(short):
                    return short
        # Otherwise find a number
        nr = 0
        while True:
            nr += 1
            short = "%s%i" % (prefix,nr)
            if not O.exists(short):
                return short


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
            break

        seen = []
        bestterm = None
        bestgain = -1
        terms = sorted(O.getTerms())    # Need the sorting
        for i in range(0,len(terms)):
            t = terms[i]
            if not (O.ignore(t) or t in seen):
                seen.append(t)
                occ = 1
                for j in range(i+1,len(terms)):
                    if terms[j] == t:
                        occ += 1
                    else:
                        break
                gain = mightAbbreviate(O,t,occ)
                if gain > bestgain:
                    bestterm = t
                    bestgain = gain

        if bestgain <= 0:
            break

        # We could do a complex thing here relating bestgain to count, but we keep it simple for now
        if count >= 10:
            break

        # Now come up with a name for it
        prefix = O.prefix(bestterm)
        short = niceName(prefix)

        # Propagate
        O.abbreviate(bestterm,short,prefix)
        count += 1

        # Iterate
       
    # close
    O.simplify()



def label_BNF():
    """
    BNF for anything that occurs as a label in dot files produced by
    Tamarin.

    This has to cover timepoints, facts, terms, as well as dot-specifics
    for record nodes (and node ports).

    Currently it is a rough overapproximation, and for example, facts are
    considered more or less interchangeable with terms. We could be more
    precise there, which would help for, e.g., not abbreviating facts but
    only their arguments.
    """

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
        langle = Literal("<")
        rangle = Literal(">")
        langleX = Literal("\<")
        rangleX = Literal("\>")
        langleBug = Literal("<").setParseAction(replaceWith("\<"))
        rangleBug = Literal(">").setParseAction(replaceWith("\>"))
        langleEsc = langleBug | langleX
        rangleEsc = rangleBug | rangleX
        dotnewline  = Literal("\l")

        quote = "'"

        def exceptfor(x):
            return "".join( [ c for c in printables if c not in x ] ) + " \t"

        CONST = Combine(Literal(quote) + Word(exceptfor(quote)) + Literal(quote))

        BASICID = Combine(Word( alphanums + "_-") + Optional(Literal(".") + Word(nums)))
        senc = Literal("senc")
        aenc = Literal("aenc")
        KEYWORD = senc | aenc
        ID = ~KEYWORD + Combine(Optional(dollar | tilde | sharp | bang) + BASICID)
        TIME = Group(akrol + Combine(sharp + BASICID))

        TERM = Forward()
        TERMLIST = TERM + ZeroOrMore(comma + TERM)
        TUPLE1 = langleEsc + TERMLIST + rangleEsc
        TUPLE2 = lparen + TERMLIST + rparen
        TUPLE = TUPLE1 | TUPLE2
        ARG = lparen + Optional(TERMLIST) + rparen
        FUNC = ID + Optional(ARG)
        ENC = (senc | aenc) + ARG
        OPERAND = Group(ENC | FUNC | TUPLE | CONST)
        TERM << OPERAND + ZeroOrMore(oneOf("^ * +") + OPERAND)

        TPAREN = lparen + TERMLIST + rparen
        TBRACK = lbrack + Optional(TERMLIST) + rbrack
        FACT = Group(Combine(Optional(bang) + ID) + Optional(TPAREN | TBRACK) + Optional(TIME))

        PORT = Combine(langle + BASICID + rangle)
        SINGLE = Optional(sharp + ID + colon) + (FACT | TERM)
        FIELDID = Group(Optional(PORT) + Optional(SINGLE))

        LABEL = Forward()
        FIELD = (lcbrack + LABEL + rcbrack) | FIELDID
        LABEL << FIELD + ZeroOrMore(rvsep + FIELD)

        labelbnf = Optional(Literal('"')) + LABEL + Optional(Literal('"')) + StringEnd()
        
        labelbnf.ignore( nbsp  )
        labelbnf.ignore( dotnewline  )
        
    return labelbnf


def render(tokens):
    if isinstance(tokens,str):
        return tokens
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
        if len(l) > 0:
            if isPort(l[0]):
                res.append(l[0])
    return res

def isTermlist(L):
    """
    Check if something is possibly a term (or a fact even)
    """
    if len(L) == 0:
        return False
    if isPort(L[0]):
        # Ignoring port spec + following
        return False
    if matchEnds(L,"{","}"):
        # Record
        return False
    if L[0] == "@":
        return False
    if L[0] == "#":
        return False
    return True


def parseLabel( strng ):

    global DEBUGMODE

    #print "*" * 40
    #print "Original: ", strng

    # First, some cleanup for displaying
    cs = strng.replace("&nbsp;"," ")
    cs = cs.replace("  "," ")
    cs = cs.replace("  "," ")
    if DEBUGMODE:
        s =  "  Parsing: %s\n" % (cs)
        appendLog(s)

    pp = pprint.PrettyPrinter(2)
    try:

        bnf = label_BNF()
        tokens = bnf.parseString( strng ).asList()

        if DEBUGMODE:
            s = "       as: %s\n" % (tokens)
            appendLog(s)

    except ParseException, err:
        s = str(err.line) + "\n"
        s +=  " "*(err.column-1) + "^" + "\n"
        s += str(err) + "\n"
        appendLog(s)
        raise
    
    #print "New     : ", render(tokens)
    #print "Ports   : ", ports(tokens)
    #print "*" * 40
    return tokens


def execDot(args,raiseErrors=False):
    """
    Invoke the real dot program

    Note that args should be a list.
    """
    import subprocess

    cmd = "dot"

    l = [cmd] + args
    s = " ".join(l)
    appendLog("Executing command: %s\n" % s)

    if raiseErrors:
        retcode = subprocess.check_call([cmd] + args)
    else:
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

    appendLog("  Using arguments: %s\n" % (str(args)))

    return args


def appendLog(l):
    global DEBUGMODE

    if DEBUGMODE:
        fp = open("/tmp/tamarin-cleandot.log",'a')
        fp.write(l)
        fp.close()

def findInputFile():

    appendLog("Scanning for input file in: "+ str(sys.argv[1:])+ "\n")

    # Currently, the Tamarin implementation is such that the filename is always the last argument.
    # This may change in the future, so a more robust parsing is maybe in order.
    infile = sys.argv[-1]

    appendLog("Using input file: %s\n" % str(infile))

    return infile


def stripQuotes(s):
    """
    Strip single or double quotes
    """

    if len(s) > 0:
        if s[0] == s[-1] and s[0] in "'\"":
            return s[1:-1]
    return s


def recordToList(s,start=0):

    """
    Consider s as an html-formatted record type string.
    Use brackets etc. to convert to "fliplist"

    Returns (fliplist,index) to just after the end of the parsed string
    """
    fl = []
    i = start
    while i < len(s):
        if s[i] == "\\":
            # Simply skip the escaped characters
            i += 2
        elif s[i] == "{":
            (fl2,i) = recordToList(s,i+1)
            fl.append(["<recordflip>"] + fl2)
            if i >= len(s):
                raise ValueError, "Cannot parse record node (missing closing parenthesis? ) [%s]" % s
            if s[i] != "}":
                raise ValueError, "Cannot parse record node (missing closing parenthesis? ) [%s]" % s
            i += 1
            start = i
        elif s[i] == "|":
            part = s[start:i].strip()
            if len(part) > 0:
                fl.append(part)
            i += 1
            start = i
        elif s[i] == "}":
            break
        else:
            i += 1

    part = s[start:i].strip()
    if len(part) > 0:
        fl.append(part)
    return (fl, i)


def listToRecord(fl):

    if isinstance(fl,str):
        return fl

    left = ""
    right = ""
    if fl[0] == "<recordflip>":
        fl = fl[1:]
        left = "{"
        right = "}"

    inner = "|".join([listToRecord(x) for x in fl])
    return "%s%s%s" % (left,inner,right)


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
    if N == None:
        return None
    sh = N.get("shape")
    if sh == None:
        return None
    if not ("record" in sh):
        return None

    label = N.get("label")
    try:
        ruleField = getSubfield(label,[1,2])
        i = ruleField.index(":")
        j = ruleField.index("[",i)

        return ruleField[i+1:j].strip()
    except:
        pass

    return None


def getNodePrefix(N):
    """
    Get node prefix up to final digit sequence or None from a Node
    """

    fullname = getRuleName(N)
    if fullname == None:
        return None

    #print "@@@%s@@@" % fullname

    i = len(fullname)
    c = 0
    while i > 0:
        if fullname[i-1].isdigit():
            c += 1
            i -= 1
        else:
            break

    if c > 0:
        # Prefix must be at least 1 character
        return fullname[:i]
    else:
        return None


def incomingEdges(G,N):
    """
    Collect incoming edges of node N
    """
    l = G.get_edge_list()
    res = []
    n = N.get_name()
    for e in l:
        if noPort(e.get_destination()) == n:
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
        if noPort(e.get_source()) == n:
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
        return G.del_node(name,index=index)

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
        return G.del_edge(src_or_list,dst=dst,index=index)
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
        
def clear_node(G,N):
    """
    Remove node N and its connected edges from the graph
    """
    print "Clearing node ", N.get_name()
    for OE in incomingEdges(G,N):
        del_edge(G,OE.get_source(),OE.get_destination())
    for OE in outgoingEdges(G,N):
        del_edge(G,OE.get_source(),OE.get_destination())

    del_node(G,N)


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
                # Unique style for newly added edges (to compensate for collapsed nodes)
                G.add_edge(Edge(src,dst,style="dashed",penwidth="2",color="#000000"))

    # Remove node
    clear_node(G,N)

    return G



def noPort(nn):
    """
    Strip port part of node name
    """
    if nn == None:
        return None
    i = nn.find(":")
    if i >= 0:
        nn = nn[:i]
    return nn


def leavePortAddress(t,coord=None):
    """
    Strip text from (non-record) label, but leave port address.
    """
    t = t.strip()
    if not t.startswith("<"):
        return ""
    i = t.find(">")
    if i < 0:
        raise ValueError, "Could not find port name end marker in [%s]" % (t)
    return t[:i+1]


def leavePortAddressExceptString(t,coord,s):
    if t == s:
        return t
    else:
        return leavePortAddress(t)


def strmap(fl,f,coord=[]):
    """
    Apply f to a strings that occur in the (nested) sequence list
    """
    if isinstance(fl,str):
        return f(fl,coord)

    nfl = []
    cnt = 0
    for x in fl:
        nfl.append(strmap(x,f,coord + [cnt]))
        cnt += 1
    return nfl


def extractStrings(fl):

    if isinstance(fl,str):
        return [fl]

    strings = []
    for x in fl:
        strings += extractStrings(x)
    return strings


def collectPorts(label):

    (fl,i) = recordToList(stripQuotes(label))
    fl = strmap(fl,leavePortAddress)
    strings = extractStrings(fl)
    ports = []
    for s in strings:
        if s != "<recordflip>":
            ports.append(s[1:-1])
    return ports


def recordSimplifyClauses(N):
    """
    Given a record node, collapse text except for rule name.
    Note that we need to leave the port names intact for the edges.
    """

    label = N.get_label()
    ruleField = getSubfield(label,[1,2]).strip()
    (fl,i) = recordToList(stripQuotes(label))
    fl = strmap(fl,lambda x,y: leavePortAddressExceptString(x,y,ruleField))
    N.set_label(listToRecord(fl))


def recordToSimpleHTML(N):
    """
    Precondition: must be a record node
    """

    label = N.get_label()
    ruleField = getSubfield(label,[1,2]).strip()
    if ruleField.startswith("<"):
        i = ruleField.find(">")
        if i > 0:
            ruleField = ruleField[i+1:].strip()

    ports = collectPorts(label)

    newlabel = "<<TABLE>\n"
    if len(ports) > 0:
        newlabel += "<TR>\n"
        for p in ports:
            newlabel += "<TD PORT=\"%s\">x</TD>\n" % (p)
        newlabel += "</TR>\n"
    newlabel += "<TR>\n"
    newlabel += "<TD COLSPAN=\"%i\">\n" % (min(1,len(ports)))
    newlabel += ruleField
    newlabel += "</TD>\n"
    newlabel += "</TR>\n"
    newlabel += "</TABLE>>"

    newlabel = "<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\"><TR><TD>x</TD></TR><TR><TD>y</TD></TR></TABLE>>"
    N.set_label(newlabel)
    print "Set [", newlabel, "] for node ",N.get_name()
    N.set_shape("plaintext")


def nodeNameStripPort(nn):
    """
    Given a node name, strip the port
    """
    i = nn.find(":")
    if i < 0:
        return nn
    else:
        return nn[:i]


def getPortLabel(G,nn):
    """
    From a compound node+port spec, get the label
    """
    if not ":" in nn:
        return None
    nxs = nn.split(":")
    nNode = nxs[0]
    nPort = "<" + nxs[1] + ">"
    for N in G.get_nodes():
        if N.get_name() == nNode:
            ss = extractStrings(recordToList(N.get_label())[0])
            for s in ss:
                sl = s.strip()
                if sl.startswith(nPort):
                    return sl[len(nPort):].strip()
    return None


def removeHideRules(G):
    """
    Remove nodes with rule names that contain "_HIDE_"
    """
    for N in G.get_nodes():
        rn = getRuleName(N)
        if rn != None:
            if "_HIDE_" in rn:
                G = removeNode(G,N)
    return G


def collapseRules(G,removeFacts=False):
    """
    Simplify rules

    If removeFacts == False, we move some things to the edges
    """
    newEdges = []
    delEdges = []
    for e in G.get_edges():
        attr = e.get_attributes()
        dstn = e.get_destination()
        srcn = e.get_source()
        if ":" in dstn + srcn:
            # Special case: do we need to retain the fact?
            if not removeFacts:
                # We retain the fact, but move it to the edge
                newlabel = getPortLabel(G,dstn)
                if newlabel == None:
                    newlabel = getPortLabel(G,srcn)
                if newlabel != None:
                    if "label" in attr.keys():
                        newlabel = attr["label"] + ", " + newlabel
                        del attr["label"]
                    attr["label"] = newlabel
            e2 = Edge(nodeNameStripPort(srcn),nodeNameStripPort(dstn),**attr)

            newEdges.append(e2)
            delEdges.append((srcn,dstn))

    for (srcn,dstn) in delEdges:
        del_edge(G,srcn,dstn)

    for e in newEdges:
        G.add_edge(e)
        
    for N in G.get_nodes():
        if isRecordNode(G,N):
            # Rewrite to simplify
            label = N.get_label()
            ruleField = getSubfield(label,[1,2]).strip()
            if ruleField.startswith("<"):
                i = ruleField.find(">")
                if i >= 0:
                    ruleField = ruleField[i+1:]
            N.set_label(ruleField)
            N.set("shape",'box')

    return G


def findNode(G,nn):
    """
    Given a node name, get the node
    """
    for n in G.get_nodes():
        if n.get_name() == nn:
            return n

    return None

def removeAllPorts(G):
    """
    Remove all port elements from edge sources and destinations.
    """
    l = G.get_edges()
    for edge in l:
        src = noPort(edge.get_source())
        dst = noPort(edge.get_destination())
        edge.set_source(src)
        edge.set_destination(dst)
    return G

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


def isRecordNode(G,N):
    """
    Is this a record node?
    """
    sh = N.get("shape")
    if sh != None:
        if "record" in sh:
            return True
    return False


def isRuleNode(G,N):
    """
    Returns True iff the node N seems to be a rule node.

    Only record nodes are 'regular' rule instances.
    """
    return isRecordNode(G,N)


def isDerivationNode(G,N):
    """
    Returns True iff the node N seems to be a derivation node.

    Only record nodes are 'regular' rule instances.
    """
    return not(isRuleNode(G,N))


def sanitizePrefix(s):
    """
    Prefixes tend to end in funny stuff. Get rid of it.
    """
    if len(s) == 0:
        return s

    # Filter what we need
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



def createCluster(G,NL,prefix="",color=None,fillcolor=None,nodecolor=None):
    """
    Given a list of node names, add a cluster for them.
    """
    (clustername,label) = makeNewWithPrefix(G,prefix=prefix)

    cluster = Cluster(clustername,label=label,style="filled",fillcolor=fillcolor,color=color)
    for nn in NL:
        n = findNode(G,nn)
        if nodecolor != None:
            n.set("fillcolor",nodecolor)
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
            pf = getNodePrefix(n)
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
    def ST(x):
        if x >= 0 and x <= 1:
            return int(255 * x)
        return 0

    (r,g,b) = c
    cstring = '#%02x%02x%02x' % (ST(r),ST(g),ST(b))
    return cstring


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


def collapseNode(G,N):
    """
    collapse a single node
    """
    N.set("label","")
    N.set("shape","point")


def isCollapsed(G,N):
    """
    Check if collapsed
    """
    return (N.get("shape") == "point")


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
            if not isCollapsed(G,N):
                if isRedundantDerivation(G,N):
                    """
                    We choose to collapse it into a point or remove it.
                    """
                    #collapseNode(G,N)
                    removeNode(G,N)
                    found = True
                    break
        if not found:
            return G






def showClusters(G):
    """
    Make clusters visible on the basis of rule prefixes.

    This function determines what should be clustered, clusters them, and provides them with a cluster background color. This makes some graphs significantly easier to grasp.

    TODO: Facts connected between in-cluster edges can simply be emptied. Basis: edge between two nodes within a single cluster needs to annotation. Nodes/ports from which all edges are not needed can be collapsed. In other words: inspect all incoming and outgoing edges. If there is none from outside the cluster, then collapse the node:port. Nodes in clusters are records anyway.
    """
    from colorsys import hls_to_rgb

    (prefixes, clusters) = findClusters(G)
    prefixes.sort()

    for (pf,cl) in clusters:
        v = Trick(pf)
        l = []
        for i in range(0,3):
            x1 = CLUSTERCOLOR1[i]
            x2 = CLUSTERCOLOR2[i]
            d = x2 - x1
            l.append((x1 + (d*v)) % 1)

        nodecolor = hexColor(hls_to_rgb(l[0],l[2],l[1]))
        backcolor = hexColor(hls_to_rgb(l[0],0.25 + 0.75 * l[2],0.5 * l[1]))
        edgecolor = hexColor(hls_to_rgb(l[0],0.6 + 0.4* l[2],0.5 * l[1]))

        createCluster(G,cl,prefix=pf,color=edgecolor,fillcolor=backcolor,nodecolor=nodecolor)

    return G


def addLegend(G,l):
    # Add the legend to the graph
    N = Node("Legend")
    N.set_label("\"%s\"" % (l))
    N.set("shape",'box')

    S = Subgraph("LegendCluster")
    S.set("rank","sink")
    S.set("style","invis")
    S.add_node(N)
    G.add_subgraph(S)

    # Drawing invisible edges from each node to the legend tends to force it to
    # the bottom, which is what we want.
    n = N.get_name()
    NL = G.get_node_list()
    for X in NL:
        x = X.get_name()
        if x not in ["edge","node"]:    # Strange pydot behaviour considers these as nodes
            E = Edge(x,n,style="invis")
            G.add_edge(E)
    return G

def abbreviateGraph(G):
    """
    Add abbreviatios to a graph

    Currently we assume only nodes have labels
    """
    # Collect labels for abbreviations into a dictionary so we can later know which label belongs to which node.
    NL = G.get_node_list()
    D = {}
    for N in NL:
        nn = N.get_name()
        label = N.get_label()
        if label not in ["",None]:
            D[nn] = parseLabel(label)
    EL = G.get_edge_list()
    for E in EL:
        en = "%s -- %s" % (E.get_source(),E.get_destination())
        label = E.get_label()
        if label not in ["",None]:
            D[en] = parseLabel(label)

    # Compute abbreviations
    R = rules(D)
    abbreviate(R)
    (D,S) = R.summary()

    # Propagate the abbreviations: overwrite node labels with their new labels.
    for N in NL:
        nn = N.get_name()
        if nn in D.keys():
            N.set_label(render(D[nn]))
    for E in EL:
        en = "%s -- %s" % (E.get_source(),E.get_destination())
        if en in D.keys():
            E.set_label(render(D[en]))

    if len(S) > 0:
        # Construct a legend text
        l = "Abbreviations\l\l"
        for (x,y) in S:
            l += "%s = %s\l" % (y,render(x))
    else:
        l = ""

    return (G,l)


def showParameters():
    """
    Parse comments dict into a text suitable for a node.
    """
    global PARAMETERS

    l = ""
    for k in PARAMETERS.keys():
        dt = PARAMETERS[k]
        dt = dt.replace("\"","\\\"")
        l += "%s: %s\\l" % (k,dt)
    if len(l) > 0:
        l = "\\lParsed PARAMETERS:\\l" + l
    return l


def getSimplificationLevel():
    """
    Find simplification level from parameters, default to 1
    """
    global PARAMETERS

    if "simplification" in PARAMETERS.keys():
        sl = PARAMETERS["simplification"]
        if sl.startswith("\"") and sl.endswith("\""):
            sl = sl[1:-1]
        return int(sl)
    return 1


def containsOutgoingEdges(G,N1,N2):
    """
    Check if the outgoing edges of N1 are contained in those of N2
    """
    for OE1 in outgoingEdges(G,N1):
        found = False
        for OE2 in outgoingEdges(G,N2):
            if OE1.get_destination() == OE2.get_destination():
                if OE1.get_label() == OE2.get_label():
                    found = True
                    break
        if not found:
            return False

    return True


def sameOutgoingEdges(G,N1,N2):
    if containsOutgoingEdges(G,N1,N2):
        if containsOutgoingEdges(G,N2,N1):
            return True
    return False


def deconstructLabel(lb):
    """
    Parse a label into a set of (stripped) lines without line breaks.
    """
    res = set()
    if lb != None:
        dt = lb.split("\l")
        for lbs in dt:
            lbss = lbs.strip()
            if len(lbss) >= 2:
                if lbss.startswith("\"") and lbss.endswith("\""):
                    lbss = lbss[1:-1]
            if len(lbss) > 0:
                res.add(lbss)
    return res

def deconstructLabels(labels):
    """
    Parse a list of labels into a set of (stripped) lines without line breaks.
    """
    res = set()
    for lb in labels:
        res |= deconstructLabel(lb)
    return res

def constructLabel(labelset):
    """
    Join a set of labels into a single label string
    """
    res = ""
    for lb in labelset:
        res += lb
        res += " \l"
    return res

def joinLabels(labels):
    """
    Join a list of labels into a single one. Elements may be 'None'.
    """
    rset = deconstructLabels(labels)
    return constructLabel(rset)


def hasIncomingEdges(G,N):
    """
    Check if a node has incoming edges
    """
    return (len(incomingEdges(G,N)) > 0)


def areSimilarRootNodes(G,N1,N2):
    """
    Check if two nodes (without incoming edges) are similar enough to be possibly joined
    """
    if hasIncomingEdges(G,N1) or hasIncomingEdges(G,N2):
        return False
    if not sameOutgoingEdges(G,N1,N2):
        return False

    # Passed all tests, consider similar
    return True


def joinSimilar(G,subsumetest=True):
    """
    Simplify graph by joining 'similar' leaf nodes and their edges.
    Returns a new graph.

    A common case is the following:

    (!KU(t1)@vkI) --[somelabel]--> X
    (!KU(t2)@vkJ) --[somelabel]--> X

    where the LHS have no other incoming/outgoing edges, but X might.

    We want to collapse these to:

    (!KU(t1)@vkI !KU(t2)@vkJ) --[somelabel]--> X

    Furthermore, if the subsumetest parameter is True, then we also remove
    edges that can be subsumed by others based on their outgoing edges and
    labels.

    Note that we are not considering nodes with an explicit color for collapsing.

    TODO: Currently we are not comparing node and edge attributes for
    similarity, which perhaps we should, to avoid losing information when
    collapsing different types of node.
    """
    AllNodes = G.get_node_list()


    RootNodes = []
    for N in AllNodes:
        if len(incomingEdges(G,N)) == 0:
            if extractNodeColor(N) == None:
                RootNodes.append(N)

    # Determine if we can merge some edges
    groups = []    # Will be a list of lists of nodes
    processed = []  # List of nodes that we already classified somehow
    for N1 in RootNodes:
        if N1 not in processed:
            # Consider this node
            group = [N1]     # Construct a local list of all similar nodes
            processed.append(N1)

            # Consider all non-processed nodes as potentially similar
            for N2 in RootNodes:
                if N2 not in processed:
                    if areSimilarRootNodes(G,N1,N2):
                        group.append(N2)
                        processed.append(N2)

            # See what we got
            if len(group) > 1:
                # There are at least two, so we could compress
                # Add this list to the "joiners" list.
                groups.append(group[:])
    

    # All groups will be merged
    toremove = []
    for group in groups:
        # We will collapse all nodes into the first element
        N1 = group[0]

        # Collect union of labels
        labels = []
        for N2 in group:
            labels.append(N2.get_label())

        # Flag all non-first nodes for removal
        for N2 in group[1:]:
            if N2 not in toremove:  # But not twice
                toremove.append(N2)

        appendLog("Parsing some labels\n")
        label = joinLabels(labels)
        if len(label) > 0:
            print "Setting label for ", N1.get_name()
            N1.set_label(label)
            N1.set_shape("box")

    # Test for subsumption?
    if subsumetest == True:

        oneFound = True
        while oneFound == True:
            candidates = []
            for x in RootNodes:
                if x not in toremove:
                    candidates.append(x)
            oneFound = False
            for N1 in candidates:
                for N2 in candidates:
                    if N1.get_name() != N2.get_name():
                        if containsOutgoingEdges(G,N1,N2):
                            # N1 can be subsumed by N2
                            label = joinLabels([N2.get_label(),N1.get_label()])
                            print "Setting label for ", N2.get_name()
                            N2.set_label(label)
                            N2.set("shape",'box')
                            if N1 not in toremove:
                                toremove.append(N1)
                            oneFound = True
                            break
                if oneFound == True:
                    break



    # Remove the nodes and their edges where needed
    for N in toremove:
        clear_node(G,N)

    return G


def removeDuplicateEdges(G):
    """
    Remove duplicate edges

    Note that we ignore different colors/styles for now, and just leave one.
    Ideally, we order these colors/styles and leave the most important one
    """
    seen = {}
    for E in G.get_edge_list():
        src = E.get_source()
        dst = E.get_destination()
        if (src,dst) in seen:
            seen[(src,dst)] += 1
        else:
            seen[(src,dst)] = 1
    for (src,dst) in seen:
        for i in range(1,seen[(src,dst)]):
            G.del_edge(src,dst,index=i)
    return G


def extractColor(S):
    """
    Extract color triplet or None.

    TODO: What if there is more than one?
    """
    if S == None:
        return None

    prefix = "COLOR"
    clen = 3
    x = S.find(prefix)
    if x < 0:
        return None

    sx = x + len(prefix)
    if sx + clen > len(S):
        return None

    cl = S[sx:sx+clen].upper()
    for i in range(0,clen):
        if not (cl[i].isdigit() or (cl[i] >= 'A' and cl[i] <= 'F')):
            # Not a color code, so skip to next candidate
            return extractColor(S[sx:])
    return cl


def extractNodeColor(N):
    """
    Extract color or none from Node
    """
    return extractColor(N.get_label())


def multiplex(S,n):
    """
    Return a string of length n * |S|, where each character is repeated n times in sequence.
    """
    SS = ""
    for c in S:
        for i in range(0,n):
            SS += c
    return SS


def colorRules(G):
    """
    Color the nodes in a graph if needed, based on the rule names.
    The rules can include "COLORrgb", where r,g,b are 0-9,A-F.
    """
    NL = G.get_node_list()
    for N in NL:
        color = extractNodeColor(N)
        if color != None:
            nodecolor = "#" + multiplex(color,2)
            N.set_fillcolor(nodecolor)
            print "Attempted to set some color!"
            print nodecolor
    return G


def improveGraph(G):
    """
    Improve a graph
    """
    global DEBUGMODE
    global PARAMETERS
    global DEBUGPARAMETERS

    legend = ""

    ### Start of graph simplification part

    sl = getSimplificationLevel()

    if sl >= 1:
        G = removeHideRules(G)
        # ShowClusters must go relatively early as it needs much information
        G = showClusters(G)
        G = collapseDerivations(G)

    if sl >= 2:
        # CollapseRules throws away a lot of information
        G = collapseRules(G,removeFacts=(sl >= 3))

    G = colorRules(G)

    ### End of graph simplification part

    # Abbreviate must go last, so that we don't abbreviate things that are later collapsed
    if "abbreviate" in PARAMETERS.keys():
        if PARAMETERS["abbreviate"] == "True":
            (G,l) = abbreviateGraph(G)
            legend += l

    if DEBUGPARAMETERS:
        legend += showParameters()

    # Add legend if needed
    if len(legend) >= 0:
        G = addLegend(G,legend)

    # TODO: The join similar simplification breaks the language conventions by
    # joining multiple lines of text. This is currently not in the BNF and
    # therefore yields an error if abbriation functions try to parse labels. We
    # should extend the BNF and call this function before doing the
    # abbreviation.
    G = joinSimilar(G)

    # Remove duplicate artifact edges
    G = removeDuplicateEdges(G)
    return G


def extractParameters(infile):
    """
    Try to extract special parameters from the file in a dict.
    """
    global PARAMETERS

    PARAMETERS = {}
    fp = open(infile,'r')
    for ll in fp.xreadlines():
        i = ll.find(":")
        if ll.startswith("// ") and i >= 0:
            key = ll[3:i].strip()
            data = ll[i+1:].strip()
            PARAMETERS[key] = data

    fp.close()

def newDot(infile):
    """
    Return a new filename with the improved graph.
    """
    from tempfile import mkstemp

    extractParameters(infile)

    (fpint,outfile) = mkstemp(suffix=".dot")
    appendLog("Producing new dot file in '%s'.\n" % outfile)

    fp = os.fdopen(fpint,'w')

    appendLog("Parsing graph from '%s'.\n" % infile)
    G = graph_from_dot_file(infile)
    if isinstance(G, list):
        G = G[0]
    if G == None:
        appendLog("Could not prase graph sensibly.\n")
        return None

    appendLog("Improving graph.\n")
    G = improveGraph(G)

    ## Remove all ports
    #G = removeAllPorts(G)

    fp.write(G.to_string())

    fp.close()

    return outfile

def main():
    # Special case for Tamarin's version check of dot
    if "--version" in sys.argv[1:] or "-V" in sys.argv[1:]:
        execDot(sys.argv[1:])

    appendLog("New run in normal case.\n")
    # Normal case
    try:
        # Try to improve the graph and run dot on the result.
        appendLog("Finding input file.\n")
        infile = findInputFile()
        appendLog("Finding args.\n")
        nargs = findArgs(infile)
        appendLog("Producing new dot file from '%s'.\n" % (infile))
        outfile = newDot(infile)
        appendLog("Running dot on the result '%s'.\n" % (outfile))
        execDot(nargs + [outfile],raiseErrors=True)
    except SystemExit:
        pass
    except:
        global DEBUGMODE

        if DEBUGMODE:
            import traceback

            print "Unexpected error:", sys.exc_info()[0]
            report = traceback.format_exc()
            appendLog(report)
            print report

        # Something went wrong, fall back to default rendering method.
        execDot(sys.argv[1:])
        pass



def TrickFilter(s):
    """
    Filter stuff we don't like and uppercase.
    """
    res = ""
    ignore = "()[]{}<>.-_="
    for c in s:
        if not c in ignore:
            res += c
    if len(res) == 0:
        res = s

    return res.upper()

def Trick(s,mfactor=9.3):
    """
    Convert a string into a float in the [0..1] range.
    """
    N = 6
    TN = 2**N

    s = TrickFilter(s)

    # value
    v = 0
    f = 1.1
    for i in range(0,len(s)):
        c = s[-(i+1)].upper()
        v += f * ord(c) 
        f = f * mfactor
    v = v % TN

    # reverse
    rv = 0
    for i in range(0,N):
        rv = 2 * rv
        if (v % 2) == 1:
            rv += 1
        v = int(v/2)

    # Convert back
    res = float(rv) / (TN-1)

    #print s,"\t",res

    return res


def OptimTrick(a,b,mfactor):
    v1 = Trick(a,mfactor=mfactor)
    v2 = Trick(b,mfactor=mfactor)
    return abs(v1-v2)


def experiment(L):
    mfactor = 1.0
    step = 0.05
    bestf = None
    bestd = 0
    while mfactor < 10:

        worstd = 1
        for (a,b) in L:
            d = OptimTrick(a,b,mfactor)
            if d < worstd:
                worstd = d

        if worstd > bestd or bestf == None:
            bestd = worstd
            bestf = mfactor
            
        mfactor += step

    print "Best we can do:"
    print "mfactor", bestf
    print "delta", bestd

if __name__ == '__main__':
    # L = [ ("A","B"), \
    #     ("Role_1","Role_2"), \
    #     ("Role1","Role2"), \
    #     ("Initiator","Responder"), \
    #     ("Init","Resp"), \
    #     ("C","S"), 
    #     ("Client","Server") ]
    # experiment(L)

    main()

