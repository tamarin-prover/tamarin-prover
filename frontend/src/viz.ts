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
    label?: string,
    // record nodes: the rectangle "x1,y1,x2,y2" of each field, separated by spaces
    rects?: string
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