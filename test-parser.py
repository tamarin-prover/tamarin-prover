#!/usr/bin/env python
#
# Pyparsing test for Tamarin dot graph labels
#

from pyparsing import \
        Literal, Word, ZeroOrMore, OneOrMore, oneOf, Group, Dict, Optional, \
        printables, alphanums, nums, ParseException, restOfLine, Forward, delimitedList, \
        nestedExpr, Keyword, Combine
import pprint


inibnf = None

def inifile_BNF():

    global inibnf
    
    if not inibnf:
        
        # Special conventions at the end:
        #
        # Sublists that start with a string element of the form "<...>" (i.e., ending with smaller than/greater than) denote port fields. We might simplify/abbreviate them later if the ports are connected within the cluster)
        #
        # Nodes are also returned as part of the dict of the parsed object. That makes it easier to reason about them.
        #
        # Sublists that start/end with curly bracket strings are the RECORD lists, and should not be considered for abbreviations
        #
        # Strings that start with '#' are timepoints and we don't want to abbreviate them either.
        #
        # We'll make a function to cover this.
        #
        #
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
        
        comment = semi + Optional( restOfLine )

        def exceptfor(x):
            return "".join( [ c for c in printables if c not in x ] ) + " \t"

        CONST = Combine(Literal(quote) + Word(exceptfor(quote)) + Literal(quote))

        nonrbrack = exceptfor("]")
        nonequals = exceptfor("=")

        senc = Literal("senc")
        aenc = Literal("aenc")
        KEYWORD = senc | aenc

        TERM = Forward()
        BASICID = Combine(Word( alphanums + "_-") + Optional(Literal(".") + Word(nums)))
        ID = ~KEYWORD + Combine(Optional(dollar | tilde | sharp) + BASICID)
        TIME = Group(akrol + Combine(sharp + BASICID))
        TERMLIST = TERM + ZeroOrMore(comma + TERM)
        TUPLE1 = Group(Literal('<') + TERMLIST + Literal('>'))
        TUPLE2 = Group(Literal('\<') + TERMLIST + Literal('\>'))
        TUPLE = TUPLE1 | TUPLE2
        ARG = Literal('(') + TERMLIST + Literal(')')
        FUNC = Group(ID + Optional(ARG))
        ENC = Group((senc | aenc) + ARG)
        TERM << (ENC | FUNC | TUPLE | CONST )

        TPAREN = lparen + TERMLIST + rparen

        TBRACK = Literal('[]')

        FACT = Group(Combine(Optional(bang) + ID) + Optional(TPAREN | TBRACK) + Optional(TIME))

        SINGLE = Optional(sharp + ID + colon) + (FACT | TERM)

        PORT = (Combine(Literal("<") + BASICID + Literal(">"))).setResultsName("port")

        FIELDID = Group(Optional(PORT) + SINGLE)

        LABEL = Forward()
        FIELD = (lcbrack + LABEL + rcbrack) | FIELDID
        LABEL << FIELD + ZeroOrMore(rvsep + FIELD)

        inibnf = LABEL

        #sectionDef = lbrack + Word( nonrbrack ) + rbrack
        #keyDef = ~lbrack + Word( nonequals ) + equals + restOfLine
        
        # using Dict will allow retrieval of named data fields as attributes of the parsed results
        #inibnf = Dict( ZeroOrMore( Group( sectionDef + Dict( ZeroOrMore( Group( keyDef ) ) ) ) ) )
        
        inibnf.ignore( nbsp  )
        inibnf.ignore( dotnewline  )
        
    return inibnf


pp = pprint.PrettyPrinter(2)

def reconstitute(tokens):
    try:
        s = ""
        for x in tokens:
            s += reconstitute(x)
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
    try:
        bnf = inifile_BNF()
        tokens = bnf.parseString( strng ).asList()
        #pp.pprint(tokens)
        ###pp.pprint( tokens.asList() )

    except ParseException, err:
        print err.line
        print " "*(err.column-1) + "^"
        print err
    
    print "*" * 40
    print "Original: ", strng
    print "New     : ", reconstitute(tokens)
    print "Ports   : ", ports(tokens)
    print "Subterms: "
    for s in subterms(tokens):
        print "  ", reconstitute(s)
    print "*" * 40
    return tokens
    
ini = test("{x}")
ini = test("{{<n30> !Ltk( $A.26, ~ltkA.26 )|<n31> !Pk( $A.26, pk(~ltkA.26) )|<n32> Out( pk(~ltkA.26) )}}")
ini = test("{{<n28> Fr( ~ltkA.26 )}|{<n29> #vr.25 : Register_pk[]}|{<n30> !Ltk( $A.26, ~ltkA.26 )|<n31> !Pk( $A.26, pk(~ltkA.26) )|<n32> Out( pk(~ltkA.26) )}}")
ini = test("!KU( senc(<'4', ~sid.4, PRF(<~pms.9, nc.7, ns.7>), nc.7, pc.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$C.4, ns.7, ps.7, $A.26>,\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(<'serverKey', nc.7, ns.7, PRF(<~pms.9, nc.7, ns.7>)>))\l) @ #vk.14\l")
ini = test("{{<n0> Fr( ~nc.4 )|<n1> St_C_0( ~sid.4, $C.4, h(\<'clientKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'serverKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>)\l)\l}|{<n2> #vr.3 : C_1[]}|{<n3> Rsend( h(\<'clientKey', nc.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\<$C.4, ~nc.4, ~sid.4, $pc.4\>\l)\l|<n4> St_C_1( $C.4, ~nc.4, ~sid.4, $pc.4,\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'clientKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'serverKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\>)\l)\l}}")


