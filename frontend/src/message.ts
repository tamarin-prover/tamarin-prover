/**
 * Messages between the interactive graph (<dot-graph-viz>, which runs in an
 * iframe or a pop-out window) and the GUI page that embeds it
 * (<dynamic-graph>).
 *
 * The GUI page lists the applicable proof methods. A method that solves a
 * goal shown in the graph carries the graph id of that goal in its link's
 * `data-goal` attribute (see graphGoalAttr in src/Web/Theory.hs):
 *
 *   graph                                    GUI page
 *     ── graph-goals-request ─────────────▶
 *     ◀──────────── graph-goals [goals] ───    the listed goals
 *     ── graph-goal-clicked id ───────────▶    clicks that method's link
 */
export type GraphGoalMessage =
    | { type: "graph-goals-request" }
    | { type: "graph-goals", goals: ListedGoal[] }
    | { type: "graph-goal-clicked", goal: string };

/** A goal of a listed proof method */
export interface ListedGoal {
    /** the graph id of the goal, from `data-goal` */
    id: string;
    /** the number of its proof method in the list, starting at 1 */
    method: number;
}

const GRAPH_GOAL_MESSAGE_TYPES: ReadonlySet<string> =
    new Set<GraphGoalMessage["type"]>(["graph-goals-request", "graph-goals", "graph-goal-clicked"]);

/** Send `message` to `target`, which must be served from the same origin. */
export function postGraphGoalMessage(target: Window, message: GraphGoalMessage): void {
    target.postMessage(message, window.location.origin);
}

/** The graph goal message carried by `event`, or null if it carries none or comes from another origin. */
export function receiveGraphGoalMessage(event: MessageEvent): GraphGoalMessage | null {
    if (event.origin !== window.location.origin) {
        return null;
    }
    const type = event.data?.type;
    return typeof type === "string" && GRAPH_GOAL_MESSAGE_TYPES.has(type)
        ? event.data as GraphGoalMessage
        : null;
}
