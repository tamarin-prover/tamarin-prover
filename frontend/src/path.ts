import { direction, print2f, Vec2 } from "./math";


export interface CubicBezierCurve {
    start: Vec2,
    control1: Vec2,
    control2: Vec2,
    end: Vec2
};

export function getCubicBezierCurveGradients(curve: CubicBezierCurve): [Vec2, Vec2] {
    return [
        direction(curve.start, curve.control1),
        direction(curve.control2, curve.end)
    ]
}

// Parse the d attributes of a path into (control) points
// for example <path d="M 10 10 C 20 20, 40 20, 50 10" stroke="black" fill="transparent" />
// has (control) points: (10, 10), (20, 20), (40, 20), (50, 10)
// * Note that the number of (floating point) numbers must be even
export function getPathPoints(path: string): Vec2[] {
    // find all (floating point) numbers
    const numbers = Array.from(path.matchAll(/-?\d+\.?\d*/g), m => parseFloat(m[0]));

    if (numbers.length % 2 === 1)
        throw new Error("The number of (floating point) numbers in \"d\" attribute must be even");

    // pair numbers into Vec2[]
    const points: Vec2[] = Array.from({ length: numbers.length / 2 }, (_, i) => ({
        x: numbers[i * 2],
        y: numbers[i * 2 + 1],
    }));

    return points;
}

// Get the points which defines a cubic Bezier curve
// * Note in case of splines (multiple Bezier curves connected together),
//   only the points which defines the gradients of the start and the end are considered
export function getCubicBezierCurve(path: string): CubicBezierCurve {
    const points = getPathPoints(path);

    if (points.length < 4)
        throw new Error("A cubic Bezier curve needs at least 4 control points");

    return {
        start: points[0],
        control1: points[1],
        control2: points[points.length - 2],
        end: points[points.length - 1]
    };
}

export function extendCurvePath(d: string, start?: Vec2, end?: Vec2): string {
    const cIndex = d.indexOf("C");
    if (cIndex === -1) {
        // no curve, return the original path
        console.error(`No curve found in the path ${d}, cannot construct new path`);
        return d;
    }
    let newD = d;
    if (start) {
        newD = `M${print2f(start)}${newD.slice(cIndex)}`;
    }
    if (end) {
        newD = newD + `L${print2f(end)}`;
    }
    return newD;
}