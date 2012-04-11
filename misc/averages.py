#!/usr/bin/env python

# Averaging out the performance tests

import sys
import commands
from optparse import OptionParser


# Awesome style: global variable
MAXNAMELEN = 0

def shortName(fn,padding=None):
    """
    Turn a filename into a nicer short name. Also updates MAXNAMELEN
    """
    global MAXNAMELEN
    
    short = fn.split("/")[-1]
    cutoffs = [".spthy"]
    for co in cutoffs:
        if short.endswith(co):
            short = short[:-len(co)]

    if len(short) > MAXNAMELEN:
        MAXNAMELEN = len(short)

    if padding == None:
        return short
    else:
        return short + (MAXNAMELEN - len(short)) * padding


def runOneTest(db,prots,i=None,proofs={},attacks={}):
    """
    Run a full batch of tests on whatever is in prots (e.g. "*.spthy") and store the results.

    db,proofs,attacks are dictionaries that map filenames to lists of things (times, proven theorems, 'attacked' theorems)

    Return (db,proofs,attacks), updated from their inputs.
    """

    cmd = "tamarin-prover --prove -Ocase-studies +RTS -N -RTS " + prots
    out = commands.getoutput(cmd)

    if i == None:
        fn = "results.txt"
    else:
        fn = "results-%i.txt" % (i)

    fp = open(fn,"w")
    fp.write(out)
    fp.close()

    fn = None
    claimblock = False
    for rawl in out.splitlines():
        """
        Here we analyze the textual output of Tamarin - this may change in future releases.

        The main possible outcomes are defined in

          Theory/Proof.hs

        where you can search for 'showProofStatus'
        """
        l = rawl.strip()
        if claimblock:
            if len(l) == 0:
                claimblock = False

            else:
                dt = l.split(":")
                if "verified" in l:
                    proofs[fn].append(dt[0])

                if "falsified" in l:
                    attacks[fn].append(dt[0])

        else:
            if "analyzed:" in l:
                fn = l.split()[-1]
                if fn not in db.keys():
                    db[fn] = []
                    shortName(fn)

            if "processing time:" in l:
                tms = l.split()[-1]
                if tms.endswith("s"):
                    tm = float(tms[:-1])
                    print fn,tm
                    db[fn].append(tm)

                else:
                    print "Expected time in [%s] from [%s]" % (tms,l)
                    sys.exit(-1)

                claimblock = True
                attacks[fn] = []
                proofs[fn] = []

    return (db,proofs,attacks)


def avgstdev(l):
    """
    Return (average,stdev,min,max) of the elements in the sequence l
    """
    
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



def runTests(prots,passes):
    """
    Run (passes) times the same time measurements for all protocols in (prots).

    Returns text string with ascii table describing the results.
    """
    db = {}
    for i in range(0,passes):
        print "Pass %i of %i" % (i+1,passes)
        (db,proofs,attacks) = runOneTest(db,prots,i)

    res = ""
    res += "Results from %i passes for %s:\n" % (passes,prots)
    res += "\n"
    for k in sorted(db.keys()):

        (avg,stdev,lmin,lmax) = avgstdev(db[k])
        res += "%s\tavg: %04.04f\tstddev: %04.04f\tmin: %04.04f\tmax: %04.04f\tP: %s\tA: %s\n" % (shortName(k," "),avg,stdev,lmin,lmax,proofs[k],attacks[k])

    return (res,db,proofs,attacks)


def findKey(db,name):
    """
    Find the first key in db that ends in name
    """
    for k in db.keys():
        if k.endswith(name):
            return k
    return None


def specialReport(db,proofs,attacks):
    """
    Generate a special report for the paper
    """
    csf12 = [
        "DH2-original.spthy", \
        "KAS1.spthy", \
        "KAS2-original.spthy", \
        "KAS2-eCK.spthy", \
        "KEA_plus_KI_KCI.spthy", \
        "KEA_plus_KI_KCI_wPFS.spthy", \
        "NAXOS_eCK.spthy", \
        "NAXOS_eCK_PFS.spthy", \
        "SignedDH_PFS.spthy", \
        "SignedDH_eCK.spthy", \
        "STS-MAC.spthy", \
        "STS-MAC-fix1.spthy", \
        "STS-MAC-fix2.spthy", \
        "JKL_TS1_2004-KI.spthy", \
        "JKL_TS1_2008-KI.spthy", \
        "JKL_TS2_2004-KI_wPFS.spthy", \
        "JKL_TS2_2008-KI_wPFS.spthy", \
        "TS3 2004/2008", \
        "UM_wPFS.spthy", \
        "UM_PFS.spthy" ]

    res = ""
    found = 0
    n = 0
    for name in csf12:
        n += 1
        k = findKey(db,"/%s" % (name))
        res += "%3i. " % (n)
        if k != None:
            found += 1
            res += shortName(k," ")
            (avg,stdev,lmin,lmax) = avgstdev(db[k])
            res += "\tavg: %6.1f" % (avg)
            res += "\tres: "
            if len(proofs[k]) > 0:
                if len(attacks[k]) > 0:
                    res += "attack (but some theorems proven)"
                else:
                    res += "proof"
            else:
                if len(attacks[k]) > 0:
                    res += "attack"
                else:
                    res += "none"

        else:
            res += "- (%s)" % (name)

        res += "\n"

    fp = open("csf12-results.txt","w")
    fp.write(res)
    fp.close()
        

def main(options,args):
    """
    Run an averaging test for the csf12 examples
    """

    prots = " ".join(args)

    (res,db,proofs,attacks) = runTests(prots,options.passes)

    fp = open("averages-results.txt","w")
    fp.write(res)
    fp.close()

    print res

    # Maybe some csf things occur in there?
    specialReport(db,proofs,attacks)

    return


def initParser():
    """
    Init the main parser.
    """

    usage = "usage %prog [options] files"

    parser = OptionParser(usage=usage)

    parser.add_option("-p", "--passes", type="int", dest="passes", default=1, help="Specify number of passes to make.")
    #parser.add_option("-f", "--file", dest="filename",
    #                  help="write report to FILE", metavar="FILE")
    #parser.add_option("-q", "--quiet",
    #                  action="store_false", dest="verbose", default=True,
    #                  help="don't print status messages to stdout")

    #parser.add_option("-m","--models", action="store", dest="models", help="Consider adversary models by name.", metavar="ID", default="paper")
    #parser.add_option("","--max-runs", action="store", dest="maxruns", help="Bound maximum number of runs.", metavar="INT", default="5")
    #parser.add_option("-d","--dir", action="append", dest="dirs", help="Set directories to scan for protocols.", metavar="PATH")
    #parser.add_option("-a","--asymmetric", action="store_true", dest="asymmetric", help="Filter to asymmetric crypto only.", default=False)
    #parser.add_option("","--ignore", action="append", dest="ignore", help="Ignore file names with this substring.", metavar="STRING")
    #parser.add_option("-s","--symmetric", action="store_true", dest="symmetric", help="Filter to symmetric crypto only.", default=False)
    #parser.add_option("","--PSH", action="append_const", const="psh", dest="graphs", help="Generate protocol-security hierarchy.")
    #parser.add_option("","--MH",  action="append_const", const="mh",  dest="graphs", help="Generate adversary-model hierarchy.")
    #parser.add_option("","--CH",  action="append_const", const="ch",  dest="graphs", help="Generate detailed combined hierarchy.")
    #parser.add_option("-l","--label", action="store", dest="label", help="Add label to output graph.")
    #parser.add_option("-g","--graphs", action="store_const", const=["psh","mh","ch"],  dest="graphs", help="Generate all graphs.")
    #parser.add_option("-A","--authentication", action="store_const", const="authentication",  dest="claimfilter", help="Restrict to authentication claims.")
    #parser.add_option("-S","--secrecy", action="store_const", const="secrecy",  dest="claimfilter", help="Restrict to secrecy claims.")
    #parser.add_option("-M","--modulo", action="store", dest="modulo", metavar="\"(MOD,IDX)\"", help="Only consider protocol claims for which (count % MOD) == IDX")
    #parser.add_option("","--cache-transitive-closure", action="store_const", const=True,  dest="closecache", default=False, help="Compute transitive closure of cached verification data.")
    #parser.add_option("-D","--debug", action="store_const", const=True,  dest="debug", default=False, help="Display debugging information.")
    #parser.add_option("","--paper", action="store_const", const=True, dest="paper", default=False, help="Repeat experiments as in paper.")
    #parser.add_option("","--paper-protocols", action="store_const", const=True, dest="paperprotocols", default=False, help="Add protocols from paper.")
    #parser.add_option("","--no-buffer", action="store_const", const=True, dest="nobuffer", default=False, help="Do not write large verification file cache.")

    (options, args) = parser.parse_args()
    if len(args) < 1:
        parser.print_usage()
        sys.exit(-1)
    return (options, args)


if __name__ == '__main__':

    # Options
    (options, args) = initParser()

    main(options,args)

