import { 
    Graph as DotGraph, 
    Node as DotNode, 
    Edge as DotEdge, 
    Attributes 
} from "@viz-js/viz"

import { 
    depth,
    JSONGraph,
    JsonGraphAbbrev,
    JSONGraphEdge,
    JSONGraphNode, 
    JSONGraphNodeFact, 
    JSONGraphNodeTermRewriter,
    isEqual,
} from "./jsongraph";
import { DotNodeLabelCell, DotNodeLabelContainer } from "./vizhtml";
import { prettierJSONGraphNodeFact } from "./prettier";

interface NodeLocation {
    name: string;
    port?: string;
}

interface FormattedFactCacheEntry {
    fact: JSONGraphNodeFact;
    label: string;
}

export class TamarinGraphBuildContext {
    nodeCount: number;
    edgeCount: number;
    portCount: number;

    nodeLocationMap: Record<string, NodeLocation> // json id -> node name;

    abbreviations: JsonGraphAbbrev[];

    abbreviationRewriter: JSONGraphNodeTermRewriter;

    formattedFactCache: Map<string, FormattedFactCacheEntry[]>;

    abbrevMap: Record<number, Set<string>>; // abbreviation index -> list of node name

    // Node IDs that appear as the source of at least one edge. Populated by
    // TamarinGraph before node construction so compact nodes can check it.
    nodesWithOutgoingEdges: Set<string> = new Set();

    constructor(abbv: JsonGraphAbbrev[]) {
        this.nodeCount = 0;
        this.edgeCount = 0;
        this.portCount = 0;
        this.nodeLocationMap = {};
        this.abbreviations = abbv;
        this.abbreviationRewriter = new JSONGraphNodeTermRewriter(
            // Sort by descending depth (deepest terms first) so nested abbreviations are
            // rewritten before their parents. Preserves the original order for equal
            // depths, as Array.sort does in the former per-term implementation.
            abbv
                .map((abbrev, index) => ({ abbrev, index, depth: depth(abbrev.jgaTerm) }))
                .sort((left, right) => right.depth - left.depth)
                .map(({ abbrev, index }) => ({
                    find: abbrev.jgaTerm,
                    replaceBy: abbrev.jgaAbbrev,
                    index,
                })),
        );
        this.formattedFactCache = new Map();
        this.abbrevMap = {};
    }

    newNodeId() {
        return this.nodeCount++;
    }

    newEdgeId() {
        return this.edgeCount++;
    }

    newPortId() {
        return this.portCount++;
    }

    currentNodeCount() {
        return this.nodeCount;
    }

    currentEdgeCount() {
        return this.edgeCount;
    }

    currentPortcount() {
        return this.portCount;
    }

    recordNode(jgnId: string, loc: NodeLocation) {
        this.nodeLocationMap[jgnId] = loc;
    }

    nodeLocation(jgnId: string) {
        const n = this.nodeLocationMap[jgnId];
        if (!n) {
            console.warn(jgnId, " not found");
        }
        return n;
    }

    recordAbbrev(abbrevIdx: number, nodeName: string) {
        if (this.abbrevMap[abbrevIdx] === undefined) {
            this.abbrevMap[abbrevIdx] = new Set<string>();
        }
        this.abbrevMap[abbrevIdx].add(nodeName);
    }
}

function abbreviate(
    nodeName: string,
    fact: JSONGraphNodeFact,
    ctx: TamarinGraphBuildContext): JSONGraphNodeFact {
    const jgnFactTerms = fact.jgnFactTerms.map(t => {
      const { term, rewrites } = ctx.abbreviationRewriter.replaceAll(t);
      rewrites.forEach(({ index }) => ctx.recordAbbrev(index, nodeName));
      return term;
    });
    return { ...fact, jgnFactTerms };
}

function equalFacts(first: JSONGraphNodeFact, second: JSONGraphNodeFact): boolean {
    return first.jgnFactName === second.jgnFactName &&
        first.jgnFactTerms.length === second.jgnFactTerms.length &&
        first.jgnFactTerms.every((term, index) => isEqual(term, second.jgnFactTerms[index]));
}

function formattedFactLabel(fact: JSONGraphNodeFact, ctx: TamarinGraphBuildContext): string {
    const cached = ctx.formattedFactCache.get(fact.jgnFactShow)
        ?.find(entry => equalFacts(entry.fact, fact));
    if (cached) {
        return cached.label;
    }

    const label = prettierJSONGraphNodeFact(fact);
    const entries = ctx.formattedFactCache.get(fact.jgnFactShow) ?? [];
    entries.push({ fact, label });
    ctx.formattedFactCache.set(fact.jgnFactShow, entries);
    return label;
}

function abbreviateAndFormatFact(
    nodeName: string,
    fact: JSONGraphNodeFact,
    ctx: TamarinGraphBuildContext,
): string {
    return formattedFactLabel(abbreviate(nodeName, fact, ctx), ctx);
}

// Abbreviates and formats each fact, joining the results with `separator`.
function formatFactList(
    facts: JSONGraphNodeFact[],
    nodeName: string,
    ctx: TamarinGraphBuildContext,
    separator: string,
): string {
    return facts.map(fact => abbreviateAndFormatFact(nodeName, fact, ctx)).join(separator);
}

// Formats facts as "[fact1,\lfact2,\l...]\l", or "" if facts is empty.
// Used for the bracketed action-list suffix shared by rect/round box node labels.
function bracketedFactList(
    facts: JSONGraphNodeFact[],
    nodeName: string,
    ctx: TamarinGraphBuildContext,
): string {
    if (facts.length === 0) {
        return "";
    }
    return "[" + formatFactList(facts, nodeName, ctx, ",\\l") + "]\\l";
}

export abstract class TamarinGraphEdge {
    jgEdge: JSONGraphEdge;
    ctx: TamarinGraphBuildContext;
    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext) {
        this.jgEdge = jgEdge;
        this.ctx = ctx;
    }
    abstract egdeAttributes(): Attributes;
    
    dot = (): DotEdge | null => ({
        tail: this.ctx.nodeLocation(this.jgEdge.jgeSource).name,
        head: this.ctx.nodeLocation(this.jgEdge.jgeTarget).name,
        attributes: {
            id: `edge${this.ctx.newEdgeId()}`, // used as svg element's id
            ...this.egdeAttributes()
        }
    })

}
export abstract class TamarinGraphNode {
    jgNode: JSONGraphNode;
    ctx: TamarinGraphBuildContext;
    nodeId: number;
    nodeName = () => `node${this.nodeId}`;

    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        this.jgNode = jgNode;
        this.ctx = ctx;
        this.nodeId = ctx.newNodeId();

        // add node id/name map record, e.g. #vk1 -> n2
        ctx.recordNode(jgNode.jgnId, {
            name: this.nodeName()
        });

        // Record every fact at its node. Record nodes replace this with a port location.
        if (this.jgNode.jgnMetadata) {
            this.jgNode.jgnMetadata.jgnPrems.forEach(f => this.recordFactNode(f));
            this.jgNode.jgnMetadata.jgnActs.forEach(f => this.recordFactNode(f));
            this.jgNode.jgnMetadata.jgnConcs.forEach(f => this.recordFactNode(f));
        }
    }
    abstract nodeAttributes(): Attributes;

    recordFactNode(fact: JSONGraphNodeFact): void {
        this.ctx.recordNode(fact.jgnFactId, {
            name: this.nodeName()
        });
    }

    recordFactPort(fact: JSONGraphNodeFact): void {
        this.ctx.recordNode(fact.jgnFactId, {
            name: this.nodeName(),
            port: `port${this.ctx.newPortId()}`
        });
    }

    dot = (): DotNode => ({
        name: this.nodeName(),
        attributes: {
            id: this.nodeName(), // used as svg element's id
            ...this.nodeAttributes()
        }
    })

}

// MARK: Rect Node

export class TamarinGraphRectBoxNode extends TamarinGraphNode {
    middleRowPort: string;
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        super(jgNode, ctx);
        if (this.jgNode.jgnMetadata) {
            this.jgNode.jgnMetadata.jgnPrems.forEach(f => this.recordFactPort(f));
            this.jgNode.jgnMetadata.jgnActs.forEach(f => this.recordFactPort(f));
            this.jgNode.jgnMetadata.jgnConcs.forEach(f => this.recordFactPort(f));
        }
        // this.color = isVaryingColor(colorMode) ? vary(color2hsv[colorMode.base]) : color2hsv[colorMode];
        // Allocate a port for the middle (rule-label) row and re-register the node ID to point to it.
        // This matches Haskell's dsNodes which resolves to the Nothing-keyed (action row) cell,
        // so that LessAtoms edges anchor at the middle row rather than the whole node bounding box.
        this.middleRowPort = `port${ctx.newPortId()}`;
        ctx.recordNode(jgNode.jgnId, { name: this.nodeName(), port: this.middleRowPort });
    }

    factsToTblRow(facts: JSONGraphNodeFact[]): DotNodeLabelContainer {
        return new DotNodeLabelContainer(
            facts.map(fact => {
                const pp = abbreviateAndFormatFact(this.nodeName(), fact, this.ctx);
                // hard fix in case of flat version i.e. if no linebreak, do not add trailing \l
                const label = pp.includes('\\l') ? pp + '\\l' : pp;
                return new DotNodeLabelCell(label, this.ctx.nodeLocation(fact.jgnFactId).port);
            })
        );
    }

    middleRow(afacts: JSONGraphNodeFact[]): DotNodeLabelCell {
        const txt = this.jgNode.jgnId + " : " + this.jgNode.jgnLabel
            + bracketedFactList(afacts, this.nodeName(), this.ctx);

        return new DotNodeLabelCell(txt, this.middleRowPort)
    }
    
    label(): string {
        if (this.jgNode.jgnMetadata) {
            const tbl = new DotNodeLabelContainer([
                this.factsToTblRow(this.jgNode.jgnMetadata.jgnPrems), // top row (premises)
                this.middleRow(this.jgNode.jgnMetadata.jgnActs), // middle row (actions)
                this.factsToTblRow(this.jgNode.jgnMetadata.jgnConcs) // bottom row (conclusions)
            ]);

            return tbl.dot();
        }
        else {
            return this.jgNode.jgnId;
        }
    }

    nodeAttributes = (): Attributes => ({
        shape: "record",
        style: "filled",
        fillcolor: this.jgNode.jgnColor || "white",
        label: this.label()
    })
}



export class TamarinGraphProtocolNode extends TamarinGraphRectBoxNode {
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        super(jgNode, ctx);
    }
}

export class TamarinGraphFreshNode extends TamarinGraphRectBoxNode {
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        super(jgNode, ctx);
    }
}

export class TamarinGraphIntruderL0Node extends TamarinGraphRectBoxNode {
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        super(jgNode, ctx);
    }
}

// MARK: Round Node

export class TamarinGraphRoundBoxNode extends TamarinGraphNode {
    borderColor: string;
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext, borderColor: string = "black") {
        super(jgNode, ctx);
        this.borderColor = borderColor;
    }

    label(): string {
        let lbl = this.jgNode.jgnId + " : " + this.jgNode.jgnLabel;

        if (this.jgNode.jgnMetadata) {
            lbl += bracketedFactList(this.jgNode.jgnMetadata.jgnActs, this.nodeName(), this.ctx);
        }
        return lbl;
    }

    nodeAttributes = (): Attributes => ({
        shape: "ellipse",
        color: this.borderColor,
        label: this.label()
    })
}

export class TamarinGraphUnknownNode extends TamarinGraphRoundBoxNode {
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        super(jgNode, ctx, );
    }

    nodeAttributes = () => ({
        label: "?"
    });
}

export class TamarinGraphLastAtomNode extends TamarinGraphRoundBoxNode {
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        super(jgNode, ctx);
    }

    nodeAttributes = () => ({
        label: this.jgNode.jgnId
    });
}

// Translate the long capitalised label from getRuleName (e.g. "Recv", "Constrc_aead")
// to the short lowercase form used by prettyIntrRuleACInfo (e.g. "irecv", "cc_aead").
function shortIntrRuleName(label: string): string {
    switch (label) {
        case 'Recv':        return 'irecv';
        case 'Send':        return 'isend';
        case 'Coerce':      return 'coerce';
        case 'FreshConstr': return 'fresh';
        case 'PubConstr':   return 'pub';
        case 'NatConstr':   return 'nat';
        case 'IEquality':   return 'iequality';
    }
    if (label.startsWith('Constr')) return label.slice('Constr'.length);
    if (label.startsWith('Destr'))  return label.slice('Destr'.length);
    return label;
}

export class TamarinGraphIntruderNode extends TamarinGraphRoundBoxNode {
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        super(jgNode, ctx);
    }

    // Matches mkNode CompactBoringNodes branch in Dot.hs:294-304:
    //   outgoingEdge → "<nodeId> : <shortName>"
    //   otherwise    → "<nodeId> : <shortName>[acts]"  (ruleLabelM form)
    label(): string {
        const shortName = shortIntrRuleName(this.jgNode.jgnLabel);
        const base = this.jgNode.jgnId + ' : ' + shortName;
        const hasOutgoing = this.ctx.nodesWithOutgoingEdges.has(this.jgNode.jgnId);
        if (hasOutgoing || !this.jgNode.jgnMetadata || this.jgNode.jgnMetadata.jgnActs.length === 0) {
            return base;
        }
        return base + bracketedFactList(this.jgNode.jgnMetadata.jgnActs, this.nodeName(), this.ctx);
    }
}

export class TamarinGraphUnsolvedActionNode extends TamarinGraphRoundBoxNode {
    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext) {
        if (jgNode.jgnMetadata?.jgnActs.at(0)?.jgnFactTag === "KUFact") {
            super(jgNode, ctx, "gray");
        } else {
            super(jgNode, ctx, "darkblue");
        }
    }

    // Matches UnsolvedActionNode branch in Dot.hs:267-272:
    //   lbl = fsep(punctuate comma facts) <-> "@" <-> nodeId
    label(): string {
        const nodeId = this.jgNode.jgnId;
        if (this.jgNode.jgnMetadata && this.jgNode.jgnMetadata.jgnActs.length > 0) {
            const acts = formatFactList(this.jgNode.jgnMetadata.jgnActs, this.nodeName(), this.ctx, ', ');
            return acts + ' @ ' + nodeId;
        }
        return this.jgNode.jgnLabel + ' @ ' + nodeId;
    }
}

// MARK: Trapezium Node

export class TamarinGraphMissingNode extends TamarinGraphNode {
    prem: boolean; // true if missingNodePrem

    constructor(jgNode: JSONGraphNode, ctx: TamarinGraphBuildContext, prem: boolean) {
        super(jgNode, ctx);
        this.prem = prem;
    }

    label(): string {
        return `${this.jgNode.jgnId}`;
    }

    nodeAttributes = (): Attributes => ({
        shape: this.prem ? "invtrapezium" : "trapezium",
        label: this.label()
    });
}

// MARK: Solid Edge

export class TamarinGraphSolidEdge extends TamarinGraphEdge {
    weight: string;
    protoperStyle: string;
    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext, weight?: string, protoperStyle?: string) {
        super(jgEdge, ctx);
        this.weight = weight!;
        this.protoperStyle = protoperStyle!;
    }

    egdeAttributes(): Attributes {
        const tailPort = this.ctx.nodeLocation(this.jgEdge.jgeSource)?.port;
        const headPort = this.ctx.nodeLocation(this.jgEdge.jgeTarget)?.port;
        return {
            style: this.protoperStyle || "solid",
            weight: this.weight || "normal",
            color: this.jgEdge.jgeColor || "black",
            ...(tailPort ? { tailport: tailPort } : {}),
            ...(headPort ? { headport: headPort } : {}),
        };
    }
}
export class TamarinGraphProtoFactEdge extends TamarinGraphSolidEdge {
    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext) {
        super(jgEdge, ctx,"10.0","bold");
    }
}
export class TamarinGraphKFactEdge extends TamarinGraphSolidEdge {
    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext) {
        super(jgEdge, ctx);
    }
}   
export class TamarinGraphPersistentFactEdge extends TamarinGraphSolidEdge {
    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext) {
        super(jgEdge, ctx, "10.0","bold");
    }
}

// default edge type if no specific relation is given
export class TamarinGraphDefaultEdge extends TamarinGraphSolidEdge {
    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext) {
        super(jgEdge, ctx);
    }
}

// MARK: Dotted Edge
export class TamarinGraphDottedEdge extends TamarinGraphEdge {
    

    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext) {
        super(jgEdge, ctx);
    }

   egdeAttributes(): Attributes {
        const tailPort = this.ctx.nodeLocation(this.jgEdge.jgeSource)?.port;
        const headPort = this.ctx.nodeLocation(this.jgEdge.jgeTarget)?.port;
        return {
            style: "dashed",
            color: this.jgEdge.jgeColor || "black",
            ...(tailPort ? { tailport: tailPort } : {}),
            ...(headPort ? { headport: headPort } : {}),
        };
    }
}

export class TamarinGraphLessAtomsEdge extends TamarinGraphDottedEdge {
    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext) {
        super(jgEdge, ctx);
    }

    dot = (): DotEdge | null => {
        const tailLoc = this.ctx.nodeLocation(this.jgEdge.jgeSource);
        const headLoc = this.ctx.nodeLocation(this.jgEdge.jgeTarget);
        if (!tailLoc || !headLoc) return null;
        return {
            tail: tailLoc.name,
            head: headLoc.name,
            attributes: {
                id: `edge${this.ctx.newEdgeId()}`,
                ...this.egdeAttributes()
            }
        };
    }
}

export class TamarinGraphUnsolvedChainEdge extends TamarinGraphDottedEdge {
    constructor(jgEdge: JSONGraphEdge, ctx: TamarinGraphBuildContext) {
        super(jgEdge, ctx);
    }
}

// MARK: Node Factory

function createTamarinGraphNode(
    jgNode: JSONGraphNode, 
    ctx: TamarinGraphBuildContext,
    simplification: number): TamarinGraphNode {
    switch (jgNode.jgnType) {
        case "isProtocolRule":
            return new TamarinGraphProtocolNode(jgNode, ctx);
        case "isIntruderRule":
        case "isISendRule":
        case "isIRecvRule":
        case "isCoerceRule":
        case "isIEqualityRule":
        case "isDestrRule":
        case "isConstrRule":
        case "isNatConstrRule":
        case "isPubConstrRule":
            if (simplification === 0) {
                return new TamarinGraphIntruderL0Node(jgNode, ctx); // blue rect box
            }
            else {
                return new TamarinGraphIntruderNode(jgNode, ctx); // round box
            }
        case "missingNodeConc":
            return new TamarinGraphMissingNode(jgNode, ctx, false);
        case "missingNodePrem":
            return new TamarinGraphMissingNode(jgNode, ctx, true);
        case "unsolvedActionAtom":
            return new TamarinGraphUnsolvedActionNode(jgNode, ctx);
        case "isFreshRule":
            return new TamarinGraphFreshNode(jgNode, ctx);
        case "lastAtom":
            return new TamarinGraphLastAtomNode(jgNode, ctx);
        case "unknown rule type":
            return new TamarinGraphUnknownNode(jgNode, ctx);
    }
}

// MARK: Edge Factory
function createTamarinGraphEdge(
    jgEdge: JSONGraphEdge, 
    ctx: TamarinGraphBuildContext): TamarinGraphEdge {
        
        switch(jgEdge.jgeRelation) {
            case "KFact":
                return new TamarinGraphKFactEdge(jgEdge, ctx);
            case "PersistentFact":
                return new TamarinGraphPersistentFactEdge(jgEdge, ctx);
            case "ProtoFact":
                return new TamarinGraphProtoFactEdge(jgEdge, ctx);
            case "LessAtoms":
                return new TamarinGraphLessAtomsEdge(jgEdge, ctx); // dotted edge
            case "unsolvedChain":
                return new TamarinGraphUnsolvedChainEdge(jgEdge, ctx); // dotted edge
            case "default":
                return new TamarinGraphDefaultEdge(jgEdge, ctx);
        }
}
export class TamarinGraph {
    jsonGraph: JSONGraph;
    ctx: TamarinGraphBuildContext;

    nodes: TamarinGraphNode[];
    edges: DotEdge[];

    constructor(jg:JSONGraph, ctx: TamarinGraphBuildContext, simplification: number) {
        this.jsonGraph = jg;
        this.ctx = ctx;

        // Edge sources are "nodeId:portId"; extract node id so compact nodes can
        // check whether they have outgoing edges (affects label format).
        // Only SystemEdges (fact-flow) count — LessAtoms/unsolvedChain are ordering edges
        // and do not suppress action-fact display (matches hasOutgoingEdge in Dot.hs:277).
        const systemEdgeRelations = new Set(['KFact', 'PersistentFact', 'ProtoFact', 'default']);
        ctx.nodesWithOutgoingEdges = new Set(
            jg.jgEdges
                .filter(e => systemEdgeRelations.has(e.jgeRelation))
                .map(e => e.jgeSource.split(':')[0])
        );

        this.nodes = this.jsonGraph.jgNodes.map(n => createTamarinGraphNode(n, ctx, simplification));

        this.edges = this.jsonGraph.jgEdges
            .map(e => createTamarinGraphEdge(e, ctx).dot())
            .filter((e): e is DotEdge => e !== null);
       
    }

    dot(): DotGraph {
        return {
            directed: this.jsonGraph.jgDirected,
            graphAttributes: {
                "nodesep": 0.3,
                "ranksep": 0.3
            },
            nodes: this.nodes.map(n => n.dot()),
            edges: this.edges
        };
    }
}