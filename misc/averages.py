#!/usr/bin/env python

# Averaging out the performance tests

import commands
import sys


def runTests(db,prots):
    cmd = "tamarin-prover --prove -Ocase-studies +RTS -N -RTS " + prots
    out = commands.getoutput(cmd)
    fn = None
    started = False
    for rawl in out.splitlines():
        l = rawl.strip()
        if started:
            if "analyzed:" in l:
                fn = l.split()[-1]
                if fn not in db.keys():
                    db[fn] = []
            if "processing time:" in l:
                tms = l.split()[-1]
                if tms.endswith("s"):
                    tm = float(tms[:-1])
                    print fn,tm
                    db[fn].append(tm)
                else:
                    print "Expected time in [%s] from [%s]" % (tms,l)
                    sys.exit(-1)
        else:
            if "summary of summaries" in l:
                started = True
    return db

def avgstdev(l):
    # Return (average,stdev,min,max) of l
    
    import math

    n = len(l)
    if l == 0:
        print "Error: list for 'avgstdev' must be at least length 1"
        sys.exit(-1)

    # Average
    lmin = l[0]
    lmax = l[0]
    s = 0.0
    for i in range(0,n):
        s = s + l[i]
        if l[i] > lmax:
            lmax = l[i]
        if l[i] < lmin:
            lmin = l[i]

    avg = s / n

    # Standard deviation
    devsum = 0
    for i in range(0,n):
        devsum = devsum + (l[i]-avg)**2
    stdev = math.sqrt(devsum / n)

    return (avg,stdev,lmin,lmax)



def main():
    """
    Run (passes) times the same time measurements for all protocols in (prots).
    """
    prots = "../examples/csf12/*.spthy"
    passes = 10

    db = {}
    for i in range(0,passes):
        print "Pass %i of %i" % (i+1,passes)
        db = runTests(db,prots)
    print "=" * 72
    print "Avg,stdev,min,max,prot"
    print "=" * 72
    for k in db.keys():
        (avg,stdev,lmin,lmax) = avgstdev(db[k])
        print "%04.04f\t%04.04f\t%04.04f\t%04.04f\t%s" % (avg,stdev,lmin,lmax,k)
    print "=" * 72


if __name__ == '__main__':
    main()

