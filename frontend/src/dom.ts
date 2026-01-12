import { select } from "d3"

export function findGElementByTitle(svg: SVGSVGElement, title: string) {
    const g = select(svg).selectAll<SVGTitleElement, unknown>("title").filter(function () {
        return this.textContent === title;
    }).node()?.parentNode as SVGGElement;
    return select(g);
}

export function findGElementIdByTitle(svg: SVGSVGElement, title?: string) {
    return title ? findGElementByTitle(svg, title).node()?.id : undefined;
}