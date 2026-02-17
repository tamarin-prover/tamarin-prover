/**
 * math.ts
 * This file contains everything you need for 2D vector math
 */

export type Vec2 = {
    /** the x component of the vector */
    x: number;
    /** the y component of the vector */
    y: number;
}

/** Ray is defined as o + td */
export interface Ray {
    /** the origin of the ray */
    o: Vec2;
    /** the direction of the ray. Note that it should be normalized */
    d: Vec2;
}


export function parseEdgeTitle(title: string): [number, number] {
    const match = title.match(/^n(\d+)(?::[^->]*)?->n(\d+)(?::[^->]*)?$/);
    if (!match || match.length < 3)
        throw new Error("Invalid edge title format, edge title must contains two node names separated by '->'");

    const from = match[1];
    const to = match[2];
    return [Number(from), Number(to)]
}


/**
 * Cast a DOMPoint into a vector (Vec2)
 * @param a the DOMPoint
 * @returns the same point as Vec2
 */
export function toVec2(a: DOMPoint): Vec2 {
    return { x: a.x, y: a.y };
}

/**
 * Inverse a vector
 * @param a a vector
 * @returns the inverse of the input vector i.e. -a
 */
export function inv(a: Vec2): Vec2 {
    return mult(a, -1);
}

/**
 * Add two vectors
 * @param a a vector
 * @param b another vector
 * @returns a + b
 */
export function add(a: Vec2, b: Vec2): Vec2 {
    return { x: a.x + b.x, y: a.y + b.y };
}

/**
 * Calculate the dot product of two vectors
 * @param a a vector
 * @param b another vector
 * @returns the dot product of a and b i.e. <a, b>
 */
export function dot(a: Vec2, b: Vec2): number {
    return a.x * b.x + a.y * b.y;
}

export function cross(a: Vec2, b: Vec2): number {
    return a.x * b.y - a.y * b.x;
}

/**
 * Calculate the squared length of a vector
 * @param a a vector
 * @returns the squared length of the input vector i.e. |a|^2 = <a, a>
 */
export function lengthSqured(a: Vec2): number {
    return dot(a, a);
}

/**
 * Scale a vector with a scalar value
 * @param a a vector
 * @param s a scalar
 * @returns s * a
 */
export function mult(a: Vec2, s: number): Vec2 {
    return { x: s * a.x, y: s * a.y };
}

/**
 * Subtract two vectors
 * @param a a vector
 * @param b another vector
 * @returns a - b
 */
export function sub(a: Vec2, b: Vec2): Vec2 {
    return add(a, inv(b));
}

/**
 * Calculate the length / L2 norm of a vector
 * @param a the input vector
 * @returns the length / L2 norm of the input vector
 */
export function len(a: Vec2) {
    return Math.sqrt(a.x * a.x + a.y * a.y);
}

/**
 * Normalize a vector
 * @param a the input vector
 * @returns the normalized input vector (divide it by its length)
 */
export function normalize(a: Vec2): Vec2 {
    return mult(a, 1 / len(a))
}

/**
 * Calculate the normalized direction vector from one point to another
 * @param a a position vector
 * @param b another position vector
 * @returns the normalized direction from point a to point b
 */
export function direction(a: Vec2, b: Vec2) {
    return normalize(sub(b, a));
}

/**
 * Traverse a certain distance along the ray
 * @param ray the ray to traverse on
 * @param t the traversing distance 
 * @returns the position after traversing a certain distance along the ray
 */
export function traverse(ray: Ray, t: number): Vec2 {
    return add(ray.o, mult(ray.d, t));
}



////////// Print Functions //////////

export function print2f(a: Vec2): string {
    return `${a.x.toFixed(2)},${a.y.toFixed(2)}`
}

export function print(a: Vec2): string {
    return `${a.x},${a.y}`
}

////////// 2D Shapes and their ray-intersection routines //////////

/** threshold for self-intersection */
const EPSILON = 1e-6;

export interface Ellipse {
    /** center of the ellipse */
    c: Vec2;
    /** x-radii of the ellipse*/
    rx: number;
    /** y-radii of the ellipse*/
    ry: number;
}

/**
 * Calculate the intersection of a ray and an ellipse
 * @param ray a ray
 * @param ellipse an ellipse
 * @returns the intersection distance along the ray, undefined if there is no intersection
 */
export function intersect(ray: Ray, { c, rx: a, ry: b }: Ellipse): number | undefined {
    const dx = ray.d.x;
    const dy = ray.d.y;
    // o - c
    const px = ray.o.x - c.x;
    const py = ray.o.y - c.y;
    const A = dx * dx * b * b + dy * dy * a * a;
    const B = 2 * (dx * px * b * b + dy * py * a * a);
    const C = px * px * b * b + py * py * a * a - a * a * b * b;
    const D = B * B - 4 * A * C;
    if (D < 0) {
        return undefined;
    }
    const t1 = (-B + Math.sqrt(D)) / (2 * A);
    const t2 = (-B - Math.sqrt(D)) / (2 * A);

    const t = Math.min(t1, t2);
    if (t < EPSILON) {
        return undefined;
    }

    return t;
}

/**
 * Calculate the radii given content and padding
 * @param contentLength the width/height of the content
 * @param padding the additive padding to the radii
 * @returns the radii
 */
export function calculateEllipseRadii(contentLength: number, padding: number) {
    return contentLength / 2 + padding;
}

/**
 * Calculate the centroid of an arbitary shape given bounding box
 * @param rect the bounding box of the shape
 * @returns the centroid position
 */
export function calculateCentroid(rect: DOMRect): Vec2 {
    return { x: rect.x + rect.width / 2, y: rect.y + rect.height / 2 };
}

export function yAxisAlignedProjection(p: Vec2, { c, rx, ry }: Ellipse): Vec2 {
    const dx = p.x - c.x;
    const radicand = ry * ry * (1 - (dx * dx) / (rx * rx));
    if (radicand <= 0)
        throw new Error("Point to be projected lies beyond ellipse's x value range")
    const y = - Math.sqrt(radicand) + c.y;
    return { x: p.x, y }
}

export function project(p: Vec2, { c, rx, ry }: Ellipse): Vec2 {
    // translate p into pp so that ellipse center is on the origin
    const pp = sub(p, c);
    const theta = Math.atan2(pp.y, pp.x);
    const cosTheta = Math.cos(theta);
    const sinTheta = Math.sin(theta);
    const k = rx * ry / Math.sqrt(ry * ry * cosTheta * cosTheta + rx * rx * sinTheta * sinTheta);
    const x = k * cosTheta;
    const y = k * sinTheta;
    return add({ x, y }, c);
}