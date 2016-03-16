#!/usr/bin/env python

"""
Proof-of-concept renderer for Tamarin JSON -> Graphviz dot
Cas Cremers, Dominik Schoop, March 2016

Facts that are longer than CONST_ABBREV characters are abbreviated.
The fact names that occur most often are colored.

Ugly hack since the only purpose is to show that the Tamarin JSON output works.
"""

import json
from collections import Counter

# minimal length of term to be abbreviated
CONST_ABBREV = 25 


def dotID(myid):
    return ''.join([c for c in myid if c not in ['#','.']])


def dotSanitize(s):
    s = s.replace("<","\\<")
    s = s.replace(">","\\>")
    return s


def dotSanitizeHtml(s):
    s = s.replace("\\<","&lt;")
    s = s.replace("\\>","&gt;")
    return s


class Legend(object):
    def __init__(self):
        self.legend = {}
        self.refnumber = {}
 
    def lookup(self,s):
        if len(s) >= CONST_ABBREV:
            if s in self.legend:
                return self.legend[s]
            else:
                abbrev = s.split('(')[0]
                if abbrev in self.refnumber:
                    self.refnumber[abbrev] += 1
                    abbrev += str(self.refnumber[abbrev])
                else:
                    self.refnumber[abbrev] = 1
                    abbrev += "1"
            self.legend[s] = abbrev
            return abbrev
        else:
            return s

    def dot(self):
        if len(self.legend) > 0:
            l = {}
            for k in self.legend.keys():
                l[self.legend[k]] = k
            s = "Legend"
            s += " [ \n"
            s += "shape = \"rectangle\",\n"
            s += "label = \"Abbreviations:\l"
            for k in sorted(l):
                s += k + " = " + l[k] + "\l\n" 
            s += "\" ];\n"
            return s;
        else:
            return ""


# legend of abbreviations used in graph
MYLEGEND = Legend()

def check(s):
    global MYLEGEND
    return MYLEGEND.lookup(s)


class Term(object):
    def __init__(self,json,parent=None):
        self.json = json
        self.parent = parent

    def show(self):
        return "?"

    def __repr__(self):
        return self.show()

    def dot(self):
        return dotSanitize(self.show())


class TermConst(Term):

    def show(self):
        return self.json["jgnConst"]


class TermFunct(Term):

    def __init__(self,json,parent=None):
        Term.__init__(self,json,parent)
        # Functions have subterms
        self.Params = []
        for p in self.json["jgnParams"]:
            self.Params.append(makeTerm(p,parent=self))

    def show(self):
        return self.json["jgnShow"]

    def dotParams(self,length=0):
       return ", ".join(map(lambda p: p.dot(), self.Params))

    def dot(self):
        funct = self.json["jgnFunct"]
        if funct == "exp":
            return self.Params[0].dot() + "^(" + self.Params[1].dot() + ")"
        elif funct == "Mult":
            return self.Params[0].dot() + "*" + self.Params[1].dot()
        else:
            return self.json["jgnFunct"] + "(" + self.dotParams() + ")"


class TermPair(TermFunct):

    def dot(self):
        if isinstance(self.parent, TermPair):
            return self.dotParams()
        else:
            return "\<" + self.dotParams() + "\>"


def makeTerm(json,parent=None):
    # Factory function to produce a Term object; may be subclass
    import sys

    if "jgnConst" in json:
        return TermConst(json,parent)
    elif "jgnFunct" in json:
        if json["jgnFunct"] == "pair":
            return TermPair(json,parent)
        else:
            return TermFunct(json,parent)

    print "Do not know how to turn json into Term:"
    print json
    sys.exit(-1)


def dotcolor(cmap,factname):
    if factname in cmap:
        return "fillcolor=" + cmap[factname]
    else:
        return ""


class Fact(object):
    def __init__(self,json):
        self.fact = json
        self.showtxt = json["jgnFactShow"]
        self.factname = json["jgnFactName"]
        self.facttag = json["jgnFactTag"]
        try:
            self.ID = json["jgnFactId"]
        except:
            self.ID = ""
        self.terms = []
        for t in json["jgnFactTerms"]:
            self.terms.append(makeTerm(t))

    def __repr__(self):
        return self.showtxt

    def dot(self,showPort=False):
        global mylegend
        s = self.factname
        s += "("
        p = []
        for t in self.terms:
            p.append(t.dot())
        s += ", ".join(p)
        s += ") "
        s = check(s)
        if showPort:
            s = "<%s> %s" % (self.ID.split(":")[1],s)
        return s

    def dotHtml(self,cmap):
        global mylegend
        if self.factname in cmap:
            color = "bgcolor=\"" + cmap[self.factname] + "\""
        else:
            color = ""
        s = self.factname
        s += "("
        p = []
        for t in self.terms:
            p.append(t.dot())
        s += ", ".join(p)
        s += ") "
        s = dotSanitizeHtml(check(s))
        return "<td port=\"%s\" %s> %s </td>" % (self.ID.split(":")[1],color,s)


def Facts(json):
    facts = []
    for x in json:
        facts.append(Fact(x))
    return facts


class Node(object):
    def __init__(self,json):
        self.ID = json["jgnId"]
        self.Type = json["jgnType"]
        self.Label = json["jgnLabel"]

        self.prems = None
        self.acts = None
        self.concs = None
        self.meta = json["jgnMetadata"]

        self.prems = Facts(self.meta["jgnPrems"])
        self.concs = Facts(self.meta["jgnConcs"])
        self.acts = Facts(self.meta["jgnActs"])

    def __repr__(self):
        s = "Node %s %s\n" % (self.ID,self.Type)
        s += "  label: " + self.Label + "\n"
        t = "  prem: "
        for x in self.prems:
            s += t + repr(x) + "\n"
        t = "  act : "
        for x in self.acts:
            s += t + repr(x) + "\n"
        t = "  conc: "
        for x in self.concs:
            s += t + repr(x) + "\n"
        return s

    def dotFacts(self,facts):
        # Sequence of facts, typically no port; commas for separators
        fl = []
        for f in facts:
            fl.append(f.dot())
        s = ", ".join(fl)
        return s

    def dotSepFacts(self,facts):
        # Boxes of facts, with ports
        fl = []
        for f in facts:
            fl.append(f.dot(showPort=True))
        return " { " + " | ".join(fl) + " } "

    def dotSepFactsHtml(self,facts,cmap):
        # Boxes of facts, with ports
        if len(facts) == 0:
            return "<tr><td> </td></tr>"
        else:
            fl = []
            for f in facts:
                fl.append(f.dotHtml(cmap))
            return "<tr>" + "".join(fl) + "</tr>"

    def dotRecord(self):
        s = ""
        # add node name
        if ":" in self.ID:
            s = self.ID.split(":")[1]
        else:
            s = dotID(self.ID)
        s += " [ \n"
        s += "shape = \"record\",\n"
        s += "label = \"{ " + self.dotSepFacts(self.prems)
        s += " | " + self.ID + " : " + self.Label + "\[ " + self.dotFacts(self.acts) + " \]"
        s += " | " + self.dotSepFacts(self.concs)
        s += " }\" ];\n"
        return s

    def dotRecordHtml(self,cmap):
        s = ""
        # add node name
        if ":" in self.ID:
            s = self.ID.split(":")[1]
        else:
            s = dotID(self.ID)
        s += " [ \n"
        s += "shape = none,\n"
        s += "label = <<table border =\"1\" cellborder=\"0\" cellspacing=\"0\">"
        s += "<tr><td><table border=\"0\" cellborder=\"1\" cellspacing=\"0\">"
        s += self.dotSepFactsHtml(self.prems,cmap)
        s += "</table></td></tr>"
        s += "<tr><td><table border=\"0\" cellborder=\"1\" cellspacing=\"0\">"
        s += "<tr><td port=\"act\">"
        s += self.ID + " : <b>" + self.Label + "</b>[ " 
        s += dotSanitizeHtml(self.dotFacts(self.acts)) + " ]</td></tr>"
        s += "</table></td></tr>"
        s += "<tr><td><table border=\"0\" cellborder=\"1\" cellspacing=\"0\">"
        s += self.dotSepFactsHtml(self.concs,cmap)
        s += "</table></td></tr>"
        s += "</table>> ];\n"
        return s

    def dotRectangle(self):
        s = ""
        # add node name
        s = dotID(self.ID)
        s += " [ \n"
        s += "shape = \"rectangle\",\n"
        s += "label = \"" + self.dotFacts(self.concs)
        s += "\" ];\n"
        return s

    def dotCircle(self):
        # add node name
        s = dotID(self.ID)
        s += " [ \n"
        s += "shape = \"ellipse\",\n"
        s += "label = \"" + self.dotFacts(self.acts) + " @ " + self.ID
        s += "\" ];\n"
        return s

    def dotCircleRule(self):
        # add node name
        s = dotID(self.ID)
        s += " [ \n"
        s += "shape = \"ellipse\",\n"
        s += "label = \"" + self.ID + " : " + self.Label + "\[ " + self.dotFacts(self.acts) + " \]"
        s += "\" ];\n"
        return s

    def needsBox(self):
        c = 0
        if len(self.prems) > 0:
            c += 1
        if len(self.concs) > 0:
            c += 1
        if len(self.acts) > 0:
            c += 1
        return (c > 1)

    def oneConcOnly(self):
        return (len(self.prems) == 0 
               and len(self.concs) == 1 
               and len(self.acts) == 0)

    def dot(self,cmap):
        if self.Type == "isIntruderRule":
            return self.dotCircleRule()   # leads to warnings since the ports used in the edges are gone
        elif self.needsBox():
            return self.dotRecordHtml(cmap)
        elif len(self.concs) > 0:
            return self.dotRectangle()
        else:
            return self.dotCircle()


class Edge(object):
    def __init__(self,json):
        self.src = json["jgeSource"]
        self.dst = json["jgeTarget"]
        self.rel = json["jgeRelation"]

    def repr(self):
        return self.dot()

    def dot(self):
        style = "solid"
        if self.rel == "LessAtoms":
            style = "dotted"
        s = "%s -> %s [style = %s]\n" % (dotID(self.src),dotID(self.dst),style)
        return s


class Graph(object):
    def __init__(self,json):
        self.nodes = set()
        self.edges = set()
        for el in json.keys():
            if el == "jgEdges":
                for e in json[el]:
                    self.edges.add(Edge(e))
            elif el == "jgNodes":
                for n in json[el]:
                    self.nodes.add(Node(n))
        # eliminate lonely FreshFacts
        nodelist = []
        for n in self.nodes:
            if n.oneConcOnly() and n.concs[0].facttag == "FreshFact":
                nodelist.append(n)
        nodeidlist = []
        for n in nodelist: 
            nodeidlist.append(n.ID)
            self.nodes.discard(n)
        edgelist = []
        for e in self.edges:
            if e.src.split(':')[0] in nodeidlist or e.dst.split(':')[0] in nodeidlist:
                edgelist.append(e)
        for e in edgelist:
            self.edges.discard(e)
        # rename source and target of lessAtom edges with src or dst being a record structure
        nodemap = {}
        for n in self.nodes:
            nodemap[n.ID] = n
        for e in self.edges:
            if e.rel == "LessAtoms":
                if (nodemap[e.src].Type == "isProtocolRule"):
                    e.src += ":act"
                if (nodemap[e.dst].Type == "isProtocolRule"):
                    e.dst += ":act"
        # rename source and target of edges where the node is no record structure (e.g. isIntruderRule)
        for e in self.edges:
            nodetypes = ["isIntruderRule", "missingNodePrem", "missingNodeConc" ]
            key = e.src.split(':')[0]
            if (nodemap[key].Type in nodetypes):
                e.src = key
            key = e.dst.split(':')[0]
            if (nodemap[key].Type in nodetypes):
                e.dst = key

    def __repr__(self):
        s = ""
        for n in self.nodes:
            s += repr(n)
        return s

    def colormap(self):
        factnames = []
        facts = []
        for n in self.nodes:
            facts = list(n.prems)
            facts.extend(n.concs)
            factnames.extend(map(lambda f: f.factname, facts))
        factnames = [x for x in factnames if x != "In" and x != "Out" and x != "Fr" and x != "!KU"]
        histokeys = [e[0] for e in Counter(factnames).most_common(3)] 
        cmap = {}
        if len(histokeys) > 0:
            cmap[histokeys[0]]="#FA5858" #"red"
        if len(histokeys) > 1:
            cmap[histokeys[1]]="#58ACFA" #"blue"
        if len(histokeys) > 2:
            cmap[histokeys[2]]="#58FA58" #"green"
        #print "Colorcoding:"
        #print cmap
        return cmap

    def dot(self):
        global MYLEGEND
        s = "digraph G {\n"
        s += "graph [ fontsize=10 ];\n"
        s += "node [ fontsize=10 ];\n"
        # determine color mapping
        cmap = self.colormap()
        for n in self.nodes:
            s += n.dot(cmap)
        for e in self.edges:
            s += e.dot()
        s += MYLEGEND.dot()
        s += "}\n"
        return s


def makeGraphs(json):
    graphs = set()
    for g in json:
        graphs.add(Graph(g))
    return graphs


def getJSON(fn):
    fp = open(fn,'r')
    x = json.load(fp)
    fp.close()
    return x


def main(infile,outfile):
    import subprocess
    import tempfile

    #fp = tempfile.NamedTemporaryFile()
    fp = open("temp","w")

    json = getJSON(infile)
    gs = makeGraphs(json["graphs"])

    for g in gs:
        fp.write(g.dot())
        #fp2=open(infile+".dot","w")
        #fp2.write(g.dot())
        #fp2.close

    name = fp.name
    fp.flush()
    
    # The "-O" switch causes a same-called outfile file with png extension
    cmd = ["dot","-Tpng","-o" + outfile,name]
    subprocess.call(cmd)

    fp.close()

if __name__ == '__main__':
    import sys

    if len(sys.argv) < 3:
        print "Usage: %s <png filename> <json filename>" % (sys.argv[0])
        exit(-1)
    # Assumes the second argument to be an appropriate json file
    infile = sys.argv[2]
    outfile = sys.argv[1]
    main(infile,outfile)

