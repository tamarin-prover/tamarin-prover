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

        print "Well..."
        nonrbrack = exceptfor("]")
        nonequals = exceptfor("=")

        print "defining ID"

        senc = Literal("senc")
        aenc = Literal("aenc")
        KEYWORD = senc | aenc

        TERM = Forward()
        BASICID = Combine(Word( alphanums + "_-") + Optional(Literal(".") + Word(nums)))
        ID = ~KEYWORD + Combine(Optional(dollar | tilde | sharp) + BASICID)
        TIME = akrol + Combine(sharp + BASICID)
        TERMLIST = TERM + ZeroOrMore(comma + TERM)
        TUPLE1 = Group(Literal('<') + TERMLIST + Literal('>'))
        TUPLE2 = Group(Literal('\<') + TERMLIST + Literal('\>'))
        TUPLE = TUPLE1 | TUPLE2
        ARG = Literal('(') + TERMLIST + Literal(')')
        FUNC = Group(ID + Optional(ARG))
        ENC = (senc | aenc) + ARG
        TERM << (ENC | FUNC | TUPLE | CONST )

        TPAREN = lparen + TERMLIST + rparen

        TBRACK = Literal('[]')

        FACT = Optional(bang) + ID + Optional(TPAREN | TBRACK) + Optional(TIME)

        PORT = Combine(Literal("<") + BASICID + Literal(">")).setResultsName("node")

        SINGLE = Optional(PORT) + Optional(sharp + ID + colon) + (FACT | TERM)

        LABEL = Forward()
        #RECORDFLIP = nestedExpr(opener = lcbrack, closer = rcbrack, content = LABEL)
        RECORDFLIP = lcbrack + LABEL + rcbrack
        RECORDLINE = ~lcbrack + ((RECORDFLIP | SINGLE) + ZeroOrMore(rvsep + (RECORDFLIP | SINGLE)))
        LABEL << ( RECORDFLIP | RECORDLINE)

        print "defined ID and TERM"

        inibnf = LABEL

        #sectionDef = lbrack + Word( nonrbrack ) + rbrack
        #keyDef = ~lbrack + Word( nonequals ) + equals + restOfLine
        
        # using Dict will allow retrieval of named data fields as attributes of the parsed results
        #inibnf = Dict( ZeroOrMore( Group( sectionDef + Dict( ZeroOrMore( Group( keyDef ) ) ) ) ) )
        
        inibnf.ignore( nbsp  )
        inibnf.ignore( dotnewline  )
        
        print "Defined inibnf"

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

def test( strng ):

    print strng
    try:
        bnf = inifile_BNF()
        tokens = bnf.parseString( strng )
        print( tokens )
        pp.pprint( tokens.asList() )

    except ParseException, err:
        print err.line
        print " "*(err.column-1) + "^"
        print err
    
    print "*" * 40
    print "Original: ", strng
    print "New     : ", reconstitute(tokens)
    print "*" * 40
    return tokens
    

ini = test("{{<n30> !Ltk( $A.26, ~ltkA.26 )|<n31> !Pk( $A.26, pk(~ltkA.26) )|<n32> Out( pk(~ltkA.26) )}}")
ini = test("{{<n28> Fr( ~ltkA.26 )}|{<n29> #vr.25 : Register_pk[]}|{<n30> !Ltk( $A.26, ~ltkA.26 )|<n31> !Pk( $A.26, pk(~ltkA.26) )|<n32> Out( pk(~ltkA.26) )}}")
ini = test("!KU( senc(<'4', ~sid.4, PRF(<~pms.9, nc.7, ns.7>), nc.7, pc.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$C.4, ns.7, ps.7, $A.26>,\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(<'serverKey', nc.7, ns.7, PRF(<~pms.9, nc.7, ns.7>)>))\l) @ #vk.14\l")
ini = test("{{<n0> Fr( ~nc.4 )|<n1> St_C_0( ~sid.4, $C.4, h(\<'clientKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'serverKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>)\l)\l}|{<n2> #vr.3 : C_1[]}|{<n3> Rsend( h(\<'clientKey', nc.7, \l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\<$C.4, ~nc.4, ~sid.4, $pc.4\>\l)\l|<n4> St_C_1( $C.4, ~nc.4, ~sid.4, $pc.4,\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'clientKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\>),\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;h(\<'serverKey', nc.7, ns.7, PRF(\<~pms.9, nc.7, ns.7\>)\l&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;\>)\l)\l}}")


