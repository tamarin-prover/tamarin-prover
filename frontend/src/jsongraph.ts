export type JSONGraphNodeTermConst = {
    jgnConst: string;
};

export type JSONGraphNodeTermFunct = {
    jgnFunct: string;
    jgnParams: JSONGraphNodeTerm[];
    // Only populated by the backend for outermost terms; omitted (undefined)
    // for nested subterms. Not read anywhere in the frontend - display
    // strings are always derived from jgnFunct/jgnParams/jgnConst instead.
    jgnShow?: string;
};

export type JSONGraphNodeTerm = JSONGraphNodeTermConst | JSONGraphNodeTermFunct;

export interface JsonGraphAbbrev {
    jgaTerm: JSONGraphNodeTerm;
    jgaAbbrev: JSONGraphNodeTerm;
    jgaExpansion: JSONGraphNodeTerm;
}

export interface JSONGraphCluster {
    jgcName: string;
    jgcNodes: JSONGraphNode[];
    jgcEdges: JSONGraphEdge[];
}

export interface JSONGraphEdge {
    jgeSource: string;
    jgeRelation: JSONGraphEdgeRelation ;
    jgeTarget: string;
    jgeColor: string;
}

export type JSONGraphEdgeRelation =
    "KFact"| 
    "PersistentFact" |
    "ProtoFact" |
    "default" |
    "LessAtoms" |
    "unsolvedChain";
    

export type JSONGraphNodeType =
    "isIntruderRule"    |
    "isDestrRule"       |
    "isIEqualityRule"   |
    "isConstrRule"      |
    "isPubConstrRule"   |
    "isNatConstrRule"   |
    "isFreshRule"       |
    "isIRecvRule"       |
    "isISendRule"       |
    "isCoerceRule"      |
    "isProtocolRule"    |
    "unknown rule type" |
    "unsolvedActionAtom"|
    "lastAtom"          |
    "missingNodeConc"   |
    "missingNodePrem";

export interface JSONGraphNode {
    jgnId: string;
    jgnType: JSONGraphNodeType;
    jgnLabel: string;
    jgnMetadata?: JSONGraphNodeMetadata;
    jgnColor?: string;
}

export interface JSONGraphNodeMetadata {
    jgnActs: JSONGraphNodeFact[];
    jgnConcs: JSONGraphNodeFact[];
    jgnPrems: JSONGraphNodeFact[];
}

export interface JSONGraphNodeFact {
    jgnFactId: string;
    jgnFactTag: string;
    jgnFactName: string;
    jgnFactMult: string;
    jgnFactTerms: JSONGraphNodeTerm[];
    jgnFactShow: string;
}

export interface JSONGraph {
    jgDirected: boolean;
    jgType: string;
    jgLabel: string;
    jgNodes: JSONGraphNode[];
    jgEdges: JSONGraphEdge[];
    jgClusters: JSONGraphCluster[];
    jgAbbrevs: JsonGraphAbbrev[];
}

export interface JSONGraphs {
    graphs: JSONGraph[];
}

/**
 * Whether term is a constant term
 */
export function isJSONGraphNodeTermConst(t: JSONGraphNodeTerm): t is JSONGraphNodeTermConst {
    return "jgnConst" in t;
}

/**
 * Whether term is a function term
 */
export function isJSONGraphNodeTermFunct(t: JSONGraphNodeTerm): t is JSONGraphNodeTermFunct {
    return "jgnFunct" in t;
}

/**
 * Compare if two terms are the same
 */
export function isEqual(t1: JSONGraphNodeTerm, t2: JSONGraphNodeTerm): boolean {
    if (isJSONGraphNodeTermConst(t1) && isJSONGraphNodeTermConst(t2)) {
        return t1.jgnConst === t2.jgnConst;
    }

    if (isJSONGraphNodeTermFunct(t1) && isJSONGraphNodeTermFunct(t2) &&
        t1.jgnFunct === t2.jgnFunct &&
        t1.jgnParams.length === t2.jgnParams.length) 
    {   
        // if two function terms have same function name and parameter length,
        // compare their parameters piecewise
        for (let i = 0; i < t1.jgnParams.length; i++) {
            if (!isEqual(t1.jgnParams[i], t2.jgnParams[i])) {
                return false;
            }
        }
        return true;
    }
    return false;
}

export function depth(t: JSONGraphNodeTerm): number {
    if (isJSONGraphNodeTermConst(t)) {
        return 1;
    }

    if (isJSONGraphNodeTermFunct(t)) {
        return 1 + Math.max(...t.jgnParams.map(p => depth(p)));
    }
    return 0;
}

export interface JSONGraphNodeTermRewrite {
    find: JSONGraphNodeTerm;
    replaceBy: JSONGraphNodeTerm;
    index: number;
}

export interface JSONGraphNodeTermRewriteResult {
    rewrites: JSONGraphNodeTermRewrite[];
    term: JSONGraphNodeTerm;
}

function rewriteKey(term: JSONGraphNodeTerm): string {
    if (isJSONGraphNodeTermConst(term)) {
        return `const\u0000${term.jgnConst}`;
    }
    return `function\u0000${term.jgnFunct}\u0000${term.jgnParams.length}`;
}

export class JSONGraphNodeTermRewriter {
    private rewritesByRoot = new Map<string, JSONGraphNodeTermRewrite[]>();

    constructor(rewrites: JSONGraphNodeTermRewrite[]) {
        rewrites.forEach(rewrite => {
            const key = rewriteKey(rewrite.find);
            const candidates = this.rewritesByRoot.get(key) ?? [];
            candidates.push(rewrite);
            this.rewritesByRoot.set(key, candidates);
        });
    }

    replaceAll(term: JSONGraphNodeTerm): JSONGraphNodeTermRewriteResult {
        const rewrites: JSONGraphNodeTermRewrite[] = [];

        const rewrite = (current: JSONGraphNodeTerm): JSONGraphNodeTerm => {
            const matching = this.rewritesByRoot.get(rewriteKey(current))
                ?.find(candidate => isEqual(current, candidate.find));
            if (matching !== undefined) {
                rewrites.push(matching);
                return matching.replaceBy;
            }
            if (isJSONGraphNodeTermConst(current)) {
                return current;
            }

            const params = current.jgnParams.map(rewrite);
            return params.some((param, index) => param !== current.jgnParams[index])
                ? { jgnFunct: current.jgnFunct, jgnParams: params, jgnShow: "" }
                : current;
        };

        return { term: rewrite(term), rewrites };
    }
}

export function prettyPrintFact(f: JSONGraphNodeFact): string {
    return `${f.jgnFactName}( ${f.jgnFactTerms.map(t => prettyPrintTerm(t)).join(", ")} )`;
}

/**
 * Pretty print terms
 * @remarks 
 * Pair functions are shown as <flattened_parameters>, for details refer to the {@link flattenPairFuncTerm} function
 * 
 * @param t term
 * @returns pretty printed term string
 * 
 */
export function prettyPrintTerm(t: JSONGraphNodeTerm): string {
    if (isJSONGraphNodeTermFunct(t)) {
        if (t.jgnFunct === "pair") {
            return `<${flattenPairFuncTerm(t).join(", ")}>`;
        }
        else {
            return `${t.jgnFunct}(${t.jgnParams?.map(n => prettyPrintTerm(n)).join()})`
        }
    }
    else if (isJSONGraphNodeTermConst(t)) {
        return t.jgnConst;
    }
    else {
        throw new Error("Unrecognized node");
    }
}

/**
 * Flatten pair function term into a list of its own pretty printed parameters
 * @remark e.g. pair(a, b) will be flattened to [a, b] 
 * 
 * nested pairs i.e. pair(pair(a, b), pair(c, d)) as [a, b, c, d].
 * 
 * but pair(a, foo(pair(b, c), d)) only as [a, foo(<b, c>, d)].
 * @param t the pair function term to be flattened
 * @returns a list of pretty printed parameters
 */
export function flattenPairFuncTerm(t: JSONGraphNodeTerm): string[] {
    if (isJSONGraphNodeTermFunct(t) && t.jgnFunct === "pair") {
        return [...flattenPairFuncTerm(t.jgnParams[0]), ...flattenPairFuncTerm(t.jgnParams[1])]
    }
    return [prettyPrintTerm(t)];
}