import "./dynamicwrapper.css"

const SESSION_STORAGE_KEY_HASPOPPED = "DYN_GRP_HASPOPPED";

export class DynamicGraphWrapper extends HTMLElement {
    popoutWindow?: Window | null;

    isPopoutWindowClosed() { return !this.popoutWindow || this.popoutWindow.closed; }

    detectPopoutClosedInterval?: number

    constructor() {
        super();
    }

    render() {
        this.innerHTML = ""; // clear
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

    connectedCallback() {
        this.render();
    }
}

customElements.define('dynamic-graph', DynamicGraphWrapper);