#!/usr/bin/env python3

"""

Drop-in preprocessor to replace pandoc's 'slice' and 'include' extensions.

E.g.:

    ~~~~ {.tamarin slice="code/Naxos.spthy" lower=16 upper=32}
    ~~~~

"""

import re

def extractexclude(l, regexp):
    """
    Take a text line, and check for the regexp, which is supposed to have one defined group.
    Extract the group if possible: if so, remove the entire regexp from the
    line and return (newline without regexp, group(1))
    If not, just return (l,None)

    This is useful for extracting values from "var=value" type strings and then
    removing them form the source string.
    """
    match = re.search(regexp,l)
    if match:
        res = match.group(1)
        # print l
        # print match.start()
        # print match.end()
        # print res
        newline = l[:match.start()] + l[match.end():]
        return (newline,res)
    else:
        return (l, None)

def includefile(filename,lower=0,upper=-1):
    """
    Return an array representing a slice of the lines of a file. If no lower
    and upper are given, return the entire file.  Indices start from zero.
    """
    fp = open(filename,'r')
    i = 0
    res = []
    for l in fp:
        if i >= lower:
            if (i <= upper or upper == -1):
                res += [l]
        i += 1
    fp.close()
    return res

def filterinput(l,filename):
    """
    Basic include function; returns array of lines including l
    """
    mid = includefile(filename)
    return [l] + mid

def filterslice(l,filename):
    """
    Slice function; extract lower and upper as well, return array including cleaned-up l
    """
    (l,res) = extractexclude(l, r'lower\s*=\s*(\d*)')
    if res != None:
        lower = int(res)
        (l,res) = extractexclude(l, r'upper\s*=\s*(\d*)')
        if res != None:
            upper = int(res)
            mid = includefile(filename,lower,upper)
            return [l] + mid
    return None

def includefilerules(filename,rules):
    """
    Return an array representing a slice of the lines of a file. If no lower
    and upper are given, return the entire file.  Indices start from zero.
    """
    fp = open(filename,'r')
    res = []
    indent = max([len(x) for x in rules]) + 4 + len(" ::= ") # default indent in ebnf file is 4
    print(indent);
    for l in fp:
        for rulename in rules:
            if (rulename + "  ::=") in l: # all rules are in a single line
                    head, *tail = l.split("| ")
                    res += [head ] + ["\n" + " "*indent + "| " + x for x in tail]
    fp.close()
    return res

def filtergrammar(l,filename):
    """
    Slice function; extract rule names, return array including cleaned-up l
    """
    (l,res) = extractexclude(l, r'rules\s*=\s*"([^"]*)"')
    if res != None:
        rules = res.split(",")
        print(rules)
        mid = includefilerules(filename,rules)
        return [l] + mid
    return None

def filtercheck(l):
    """
    Check for l for any relevant filters and execute
    """
    (l, res) = extractexclude(l, r'include\s*=\s*"([^"]*)"')
    if res != None:
        return filterinput(l,res)
    (l, res) = extractexclude(l, r'slice\s*=\s*"([^"]*)"')
    if res != None:
        return filterslice(l,res)
    (l, res) = extractexclude(l, r'grammar\s*=\s*"([^"]*)"')
    if res != None:
        return filtergrammar(l,res)
    
    return None


def filter(infn,outfn):
    """
    Check for codeblock which might contain filters
    """
    codeblock = "~~~~"

    fpi = open(infn, 'r')
    res = []
    for l in fpi:
        res += [l]
        if l.startswith(codeblock):
            if len(res) >= 2:
                if res[-2].startswith(codeblock):
                    ins = filtercheck(res[-2])
                    if ins != None:
                        res = res[:-2] + ins + [l]

    fpi.close()

    fpo = open(outfn, 'w')
    for l in res:
        fpo.write(l)
    fpo.close()

def main():
    """
    ./filter.py infile outfile

    Read argument one, produce argument two
    """
    import sys

    if len(sys.argv) >= (1+2):
        filter(sys.argv[1],sys.argv[2])
    else:
        print("Need two arguments: infile and outfile.")

if __name__ == '__main__':
    main()


