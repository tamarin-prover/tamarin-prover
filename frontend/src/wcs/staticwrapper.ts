import "./staticwrapper.css"

export class StaticGraphWrapper extends HTMLElement {
    constructor() {
        super();
    }

    connectedCallback() {
        const graphSrc = this.getAttribute("graphSrc");

        if (!graphSrc) {
            console.error("[StaticGraphWrapper]: Empty dotsrc");
            return;
        }

        const iframe = document.createElement("iframe");
        iframe.setAttribute("src", graphSrc);
        iframe.setAttribute("width", "100%");
        iframe.setAttribute("height", "400");

        const a = document.createElement("a");
        a.setAttribute("href", graphSrc);
        a.setAttribute("target", "_blank");
        a.innerText = "Open Graph in New Tab";

        this.append(iframe);
        this.append(a);
    }
}

customElements.define('static-graph', StaticGraphWrapper);