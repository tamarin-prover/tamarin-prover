export interface VizEdge {
    _gvid: number,
    tail: number,
    tailport?: string,
    head: number,
    headport?: string,
    style?: VizEdgeStyle
}

export interface VizObject {
    _gvid: number,
    _ldraw_?: VizObjectDraw[],
    name: string,
    shape: VizNodeShape,
    label?: string
}

export interface VizObjectDraw {
    op: VizObjectDrawOp,
    text?: string,
}

export type VizObjectDrawOp = "F" | "c" | "T" | "S" | "p"

export interface VizGraph {
    edges?: VizEdge[]
    objects: VizObject[]
}

export type VizEdgeStyle = "invis" | "bold"
export type VizNodeShape = "plain" | "ellipse" | "record" | "invtrapezium" | "trapezium"