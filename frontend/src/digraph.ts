import { findGElementIdByTitle } from "./dom"
import { VizGraph } from "./viz"

interface DiEdge {
    elementId?: string,
    minimizable: boolean,
    title?: string,
    from: string,
    fromPort?: string,
    to: string
    toPort?: string
}

interface DiNode {
    title: string,
    elementId?: string,
    minimizable: boolean
}


type NodeDict = { [key: string]: DiNode };
type EdgeDict = { [key: string]: DiEdge };

// the value represents edge id
type AdjMatrix = { [key: string]: AdjMatrixRow };
type AdjMatrixRow = { [key: string]: string | null };


export interface DiGraphConnections {
    nodes: string[],
    edges: string[]
}

function composeEdgeTitle(edge: DiEdge, nodes: NodeDict) {
    return `${nodes[edge.from].title}${edge.fromPort ? `:${edge.fromPort}` : ""}->${nodes[edge.to].title}${edge.toPort ? `:${edge.toPort}` : ""}`;
}

export class DiGraph {

    nodes: NodeDict;
    edges: EdgeDict;
    adj: AdjMatrix;
    abbrev: {
        elementId?: string,
        abbreviations: { [key: string]: string[] }
    } = {
            abbreviations: {}
        };

    // table uses elementId as key to lookup (node/edge)Id
    reverseLookup: {
        nodes: { [key: string]: string },
        edges: { [key: string]: string }
    } = {
            nodes: {},
            edges: {}
        }

    //extract abbreviations
    constructor(vizGraph: VizGraph, svg: SVGSVGElement) {
        const abbrevObj = (vizGraph.objects ?? []).find(n => n.shape === "plain");
        if (abbrevObj) {
            // find abbreviation table's element id
            this.abbrev.elementId = findGElementIdByTitle(svg, abbrevObj.name);
            // extract abbreviations
            abbrevObj._ldraw_?.filter(d => d.op === "T").forEach((d, i) => {
                if (i % 3 === 0 && d.text) {
                    this.abbrev.abbreviations[d.text] = [];
                }
            });
        }


        // extract nodes
        this.nodes = (vizGraph.objects ?? []).filter(n =>
            n.shape === "ellipse" ||
            n.shape === "record" ||
            n.shape === "invtrapezium" ||
            n.shape === "trapezium"
        ).reduce(
            (acc, cur) => {
                // check if node contains abbrevation
                Object.keys(this.abbrev.abbreviations).forEach(k => {
                    if (cur.label?.includes(k)) {
                        this.abbrev.abbreviations[k].push(cur._gvid.toString());
                    }
                });
                acc[cur._gvid] = {
                    title: cur.name,
                    minimizable: cur.shape === "record"
                }
                return acc
            }, {} as NodeDict
        );

        // extract edges
        this.edges = (vizGraph.edges ?? []).filter(e => e.style !== "invis" &&
            this.nodes[e.tail.toString()] !== undefined &&
            this.nodes[e.head.toString()] !== undefined)
            .reduce((acc, cur) => {
                const fromNodeId = cur.tail.toString();
                const toNodeId = cur.head.toString();
                acc[cur._gvid] = {
                    from: fromNodeId,
                    fromPort: cur.tailport,
                    to: toNodeId,
                    toPort: cur.headport,
                    minimizable: this.nodes[fromNodeId].minimizable || this.nodes[toNodeId].minimizable
                };
                return acc;

            }, {} as EdgeDict);

        // initialize adjacency matrix
        this.adj = Object.keys(this.nodes).reduce((accRow, curRow) => {
            accRow[curRow] = Object.keys(this.nodes).reduce((acc, cur) => {
                acc[cur] = null;
                return acc;
            }, {} as AdjMatrixRow);
            return accRow;
        }, {} as AdjMatrix);

        // construct adjacency matrix
        for (const [k, v] of Object.entries(this.edges)) {
            this.adj[v.from][v.to] = k;
        }

        // construct edge titles
        this.edges = Object.keys(this.edges).reduce(
            (acc, curKey) => {
                const e = this.edges[curKey];
                acc[curKey] = {
                    ...e,
                    title: composeEdgeTitle(e, this.nodes)
                };
                return acc;
            }, {} as EdgeDict
        );

        // find and assign element id
        this.nodes = Object.keys(this.nodes).reduce(
            (acc, curKey) => {
                const n = this.nodes[curKey];
                const elementId = findGElementIdByTitle(svg, n.title);
                acc[curKey] = {
                    ...n,
                    elementId
                };
                if (elementId) {
                    this.reverseLookup.nodes[elementId] = curKey
                }
                return acc;
            }, {} as NodeDict
        );

        this.edges = Object.keys(this.edges).reduce(
            (acc, curKey) => {
                const e = this.edges[curKey];
                const elementId = findGElementIdByTitle(svg, e.title);
                acc[curKey] = {
                    ...e,
                    elementId
                }
                if (elementId) {
                    this.reverseLookup.edges[elementId] = curKey
                }
                return acc;
            }, {} as EdgeDict
        );
    }

    getConnections(nodeId: string): DiGraphConnections {
        // downstream connections only
        const connections: DiGraphConnections = {
            nodes: [nodeId],
            edges: []
        };
        for (const [n, e] of Object.entries(this.adj[nodeId])) {
            if (e) {
                connections.edges.push(e); // Note* inplace/mutable change
                const downstreamConnnections = this.getConnections(n);
                connections.edges = connections.edges.concat(downstreamConnnections.edges); // Note* concat is immutable
                connections.nodes = connections.nodes.concat(downstreamConnnections.nodes);
            }
        }
        return connections;
    }
}