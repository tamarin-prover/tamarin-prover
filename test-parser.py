#!/usr/bin/env python
#
# Pyparsing test for Tamarin dot graph labels
#

from pyparsing import \
        Literal, Word, ZeroOrMore, OneOrMore, oneOf, Group, Dict, Optional, \
        printables, alphanums, nums, ParseException, restOfLine, Forward, delimitedList, \
        nestedExpr, Keyword, Combine
import pprint


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
        dotnewline  = (Literal("\l") | Literal("\\l"))

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
        TUPLE = TUPLE1 | TUPLE2
        ARG = Literal('(') + TERMLIST + Literal(')')
        FUNC = Group(ID + Optional(ARG))
        ENC = Group((senc | aenc) + ARG)
        TERM << (ENC | FUNC | TUPLE | CONST )

        TPAREN = lparen + TERMLIST + rparen
        #TBRACK = Literal('[]')
        TBRACK = lbrack + Optional(TERMLIST) + rbrack
        FACT = Group(Combine(Optional(bang) + ID) + Optional(TPAREN | TBRACK) + Optional(TIME))

        PORT = Combine(Literal("<") + BASICID + Literal(">"))
        SINGLE = Optional(sharp + ID + colon) + (FACT | TERM)
        FIELDID = Group(Optional(PORT) + SINGLE)

        LABEL = Forward()
        FIELD = (lcbrack + LABEL + rcbrack) | FIELDID
        LABEL << FIELD + ZeroOrMore(rvsep + FIELD)

        labelbnf = LABEL
        
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
    

def test( strng ):

    print strng

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
    
    print "*" * 40
    print "Original: ", strng
    print "New     : ", render(tokens)
    print "Ports   : ", ports(tokens)
    print "Subterms: "
    for s in sorted(subterms(tokens)):
        print "  ", render(s)
    print "*" * 40
    return tokens
    
# ini = test("{x}")
# ini = test("{{<n30> !Ltk( $A.26, ~ltkA.26 )|<n31> !Pk( $A.26, pk(~ltkA.26) )|<n32> Out( pk(~ltkA.26) )}}")
# ini = test("{{<n28> Fr( ~ltkA.26 )}|{<n29> #vr.25 : Register_pk[]}|{<n30> !Ltk( $A.26, ~ltkA.26 )|<n31> !Pk( $A.26, pk(~ltkA.26) )|<n32> Out( pk(~ltkA.26) )}}")
# ini = test("!KU( senc(<'4', ~sid.4, PRF(<~pms.9, nc.7, ns.7>), nc.7, pc.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$C.4, ns.7, ps.7, $A.26>,\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(<'serverKey', nc.7, ns.7, PRF(<~pms.9, nc.7, ns.7>)>))\l) @ #vk.14\l")
TEST = "{{<n6> St_C_2( $A.26, $C.4, ~sid.4, nc.7, pc.7, ns.7,\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ps.7, ~pms.9,\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'clientKey', nc.7, ns.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;PRF(\<~pms.9, nc.7, ns.7\>)\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'serverKey', nc.7, ns.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;PRF(\<~pms.9, nc.7, ns.7\>)\>)\l)\l|<n7> Rrecv( h(\<'serverKey', nc.7, ns.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;PRF(\<~pms.9, nc.7, ns.7\>)\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\<'4', ~sid.4, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;PRF(\<~pms.9, nc.7, ns.7\>), nc.7, pc.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$C.4, ns.7, ps.7, $A.26\>\l)\l}|{<n8> #vr.6 : C_3[Commit( $C.4, $A.26,\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\<'client', PRF(\<~pms.9, nc.7, ns.7\>), \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'serverKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>), \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'clientKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>)\>\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;SessionKeys( $A.26, $C.4, h(\<'serverKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'clientKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>)\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;)]\l}|{<n9> St_C_0( ~sid.4, $C.4, h(\<'clientKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'serverKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>)\l)\l}}"

L = test(TEST)

O = rules({ '1': L})
abbreviate(O)
(D,S) = O.summary()

print "*" * 70
print render(L)
print render(D['1'])
print "*" * 70


