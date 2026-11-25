import "./dynamicwrapper.css"
import { postGraphGoalMessage, receiveGraphGoalMessage } from "../message";

const SESSION_STORAGE_KEY_HASPOPPED = "DYN_GRP_HASPOPPED";

/** Links of proof methods that solve a goal shown in the graph (see message.ts). */
const GOAL_LINK_SELECTOR = "a.proof-method[data-goal]";

/**
 * The link of the first listed proof method for each goal id. The list is
 * ranked, so this is the highest-ranked method if several solve the same goal.
 */
function goalLinks(): Map<string, HTMLElement> {
    const links = new Map<string, HTMLElement>();
    for (const link of document.querySelectorAll<HTMLElement>(GOAL_LINK_SELECTOR)) {
        const goal = link.dataset.goal!;
        if (!links.has(goal)) {
            links.set(goal, link);
        }
    }
    return links;
}

/**
 * Shows the graph of the current constraint system in an iframe or a
 * pop-out window, and lets the graph apply the listed proof methods of the
 * goals it shows: it answers the graph's goal messages (see message.ts).
 */
export class DynamicGraphWrapper extends HTMLElement {
    popoutWindow?: Window | null;
    iframe?: HTMLIFrameElement;

    isPopoutWindowClosed() { return !this.popoutWindow || this.popoutWindow.closed; }

    detectPopoutClosedInterval?: number

    constructor() {
        super();
    }

    render() {
        this.innerHTML = ""; // clear
        this.iframe = undefined;
        if (this.detectPopoutClosedInterval !== undefined) {
            clearInterval(this.detectPopoutClosedInterval); // always remove interval task
        }

        const graphSrc = this.getAttribute("graphSrc");
        if (!graphSrc) {
            console.error("[DynamicGraphWrapper]: Empty dotsrc");
            return;
        }

        const hasPopped = sessionStorage.getItem(SESSION_STORAGE_KEY_HASPOPPED) === "true";

        if (hasPopped) {
            this.popoutWindow = window.open(graphSrc, "dynamicGraphPopout", "popup"); // open automatically
            const closeBtn = document.createElement("button");
            closeBtn.innerText = "Pop In";
            closeBtn.addEventListener("click" , _ => {
                if (!this.isPopoutWindowClosed()) {
                    this.popoutWindow!.close();
                    sessionStorage.setItem(SESSION_STORAGE_KEY_HASPOPPED, "false");
                }
                this.render();
            });
            this.append(closeBtn);

            this.detectPopoutClosedInterval = setInterval(() => {
                // detect if popout closed every 1s
                if (this.isPopoutWindowClosed()) {
                    sessionStorage.setItem(SESSION_STORAGE_KEY_HASPOPPED, "false");
                    this.render();
                }
            }, 1000);
        }
        else {
            const iframe = document.createElement("iframe");
            iframe.setAttribute("src", graphSrc);
            iframe.setAttribute("width", "100%");
            iframe.setAttribute("height", "400");
            this.append(iframe);
            this.iframe = iframe;

            const openBtn = document.createElement("button");
            openBtn.innerText = "Pop Out";
            openBtn.addEventListener("click", _ => {
                this.popoutWindow = window.open(graphSrc, "dynamicGraphPopout", "popup"); // open manually
                if (this.popoutWindow && !this.popoutWindow.closed) {
                    sessionStorage.setItem(SESSION_STORAGE_KEY_HASPOPPED, "true");
                    this.render();
                }
            });
            this.append(openBtn);
        }        
    }

    /** Whether `source` is the window that shows this element's graph. */
    isGraphWindow(source: MessageEventSource | null): source is Window {
        return source !== null &&
            (source === this.iframe?.contentWindow || source === this.popoutWindow);
    }

    handleGraphMessage = (event: MessageEvent) => {
        if (!this.isGraphWindow(event.source)) {
            return;
        }
        const message = receiveGraphGoalMessage(event);
        switch (message?.type) {
            case "graph-goals-request":
                postGraphGoalMessage(event.source, { type: "graph-goals", goals: [...goalLinks().keys()] });
                break;
            case "graph-goal-clicked":
                // exactly as if the user clicked the proof method in the list
                goalLinks().get(message.goal)?.click();
                break;
        }
    };

    connectedCallback() {
        window.addEventListener("message", this.handleGraphMessage);
        this.render();
    }

    disconnectedCallback() {
        window.removeEventListener("message", this.handleGraphMessage);
    }
}

customElements.define('dynamic-graph', DynamicGraphWrapper);