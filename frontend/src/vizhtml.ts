import { HTMLString } from "@viz-js/viz";

export type VizHtmlTag = 
    "TABLE" | 
    "TR"    | 
    "TD"    |
    "BR"    |
    "I"     |
    "B"     |
    "U"     |
    "O"     |
    "SUB"   |
    "SUP"   |
    "S";


export type VizHtmlAttributes = { [name: string]: string | number | undefined };

export abstract class VizHtmlElement {
    abstract html(): HTMLString;
}

export abstract class VizHtmlTagElement extends VizHtmlElement {
    abstract readonly tag: VizHtmlTag;
    abstract html(): HTMLString;
}

/**
 * Empty Tag Element
 * 
 * It doesn't have content
 * 
 * e.g. `<BR/>`
 */
export abstract class VizHtmlEmptyElement extends VizHtmlTagElement {
    abstract readonly tag: VizHtmlTag;
    html = () => ({ html: `<${this.tag}/>` });
}

export class VizHtmlLineBreakElement extends VizHtmlEmptyElement {
    tag: VizHtmlTag = "BR";
}

/**
 * Container Tag Element
 * 
 * Its content is always enclosed by a start tag and a close tag
 * 
 * e.g. `<TABLE>...</TABLE>`
 */
export abstract class VizHtmlContainerElement extends VizHtmlTagElement {
    abstract readonly tag: VizHtmlTag;
    abstract content: VizHtmlElement | VizHtmlElement[] | null;
    attributes: VizHtmlAttributes | null = null;

    htmlAttributes = () => this.attributes !== null && Object.entries(this.attributes).length > 0 ?
        " " + Object.entries(this.attributes).map(([name, value]) => `${name.toUpperCase()}="${value}"`).join(" ") : "";

    htmlContent = () => this.content !== null ? 
            (Array.isArray(this.content) ? 
            this.content.map(c => c.html().html).join("") : // VizHtmlElement[] case
            this.content.html().html ) : // VizHtmlElement case
            "";  // null case

    html() {
        return {
            html: `<${this.tag}${this.htmlAttributes()}>${this.htmlContent()}</${this.tag}>`
        };
    }
}

export interface VizHtmlTableElementAttributes extends VizHtmlAttributes {
    border?: number;
    cellborder?: number;
    cellpadding?: number;
    cellspacing?: number;
}

export class VizHtmlTableElement extends VizHtmlContainerElement {
    tag: VizHtmlTag = "TABLE";
    content: VizHtmlRowElement | VizHtmlRowElement[] | null;
    attributes: VizHtmlTableElementAttributes | null;
    constructor(content: VizHtmlRowElement | VizHtmlRowElement[] | null, attributes: VizHtmlTableElementAttributes | null = null) {
        super();
        this.content = content;
        this.attributes = attributes;
    }
}

export class VizHtmlRowElement extends VizHtmlContainerElement  {
    tag: VizHtmlTag = "TR";
    content: VizHtmlCellElement | VizHtmlCellElement[] | null;
    constructor(content: VizHtmlCellElement | VizHtmlCellElement[] | null) {
        super();
        this.content = content;
    }
}

export abstract class VizHtmlTextContainerElement extends VizHtmlContainerElement {
    abstract readonly tag: VizHtmlTag;
    content: VizHtmlTextElement | VizHtmlTextElement[] | null;
    constructor(content: VizHtmlTextElement | VizHtmlTextElement[] | null) {
        super();
        this.content = content;
    }
}
export interface VizHtmlCellElementAttributes extends VizHtmlAttributes {
    port?: string;
    colspan?: number;
}
export class VizHtmlCellElement extends VizHtmlTextContainerElement  {
    tag: VizHtmlTag = "TD";
    attributes: VizHtmlCellElementAttributes | null;
    constructor(content: VizHtmlTextElement | VizHtmlTextElement[] | null, attributes: VizHtmlCellElementAttributes | null = null) {
        super(content);
        this.attributes = attributes;
    }

}

export class VizHtmlItalicElement extends VizHtmlTextContainerElement  {
    tag: VizHtmlTag = "I";
}

export class VizHtmlBoldElement extends VizHtmlTextContainerElement  {
    tag: VizHtmlTag = "B";
}

export class VizHtmlUnderlineElement extends VizHtmlTextContainerElement  {
    tag: VizHtmlTag = "U";
}

export class VizHtmlOverlineElement extends VizHtmlTextContainerElement  {
    tag: VizHtmlTag = "O";
}

export class VizHtmlSubscriptElement extends VizHtmlTextContainerElement  {
    tag: VizHtmlTag = "SUB";
}

export class VizHtmlSuperscriptElement extends VizHtmlTextContainerElement  {
    tag: VizHtmlTag = "SUP";
}

export class VizHtmlStrikethroughElement extends VizHtmlTextContainerElement  {
    tag: VizHtmlTag = "S";
}

function escapeHtml(unsafe: string) {
  return unsafe
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#039;");
}

export class VizHtmlStringElement extends VizHtmlElement {
    str: string;
    constructor(str: string) {
        super();
        this.str = str;
    }
    html = () => ({ html: escapeHtml(this.str) });
}

export type VizHtmlTextElement = VizHtmlStringElement
    | VizHtmlLineBreakElement
    | VizHtmlItalicElement
    | VizHtmlBoldElement
    | VizHtmlUnderlineElement
    | VizHtmlOverlineElement
    | VizHtmlSubscriptElement
    | VizHtmlSuperscriptElement
    | VizHtmlStrikethroughElement;

abstract class DotNodeLabelBase {
    abstract dot(): string;
}

export class DotNodeLabelContainer extends DotNodeLabelBase {
    children: DotNodeLabelBase[];
    constructor(children: DotNodeLabelBase[]) {
        super();
        this.children = children;
    }
    dot = () => {
        const rows = this.children.map(c => c.dot()).filter(Boolean);
        return rows.length === 0 ? "" :  `{${rows.join("|")}}`
    };
}

export class DotNodeLabelCell extends DotNodeLabelBase {
    portName?: string;
    text: string;
    constructor(text: string, portName?: string) {
        super();
        this.portName = portName;
        this.text = text;
    }
    dot = () => `{${this.portName ? ("<" + this.portName + "> ") : ""}${escapeHtml(this.text)}}`;
}
