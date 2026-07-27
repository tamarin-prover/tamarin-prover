import { instance, Graph as DotGraph } from "@viz-js/viz";
import { select, selectAll, zoom, create, D3ZoomEvent } from "d3";
import { extendCurvePath, getCubicBezierCurve, getCubicBezierCurveGradients } from "../path";
import { calculateCentroid, cross, direction, dot, Ellipse, intersect, inv, print2f, project, Ray, sub, traverse, Vec2 } from "../math";
import { VizGraph } from "../viz";
import { DiGraph, DiGraphConnections } from "../digraph";
import './graph.css';
import { JSONGraphs, prettyPrintTerm } from "../jsongraph";
import { TamarinGraph, TamarinGraphBuildContext } from "../tmgraph";
import { prettierJSONGraphNodeTerm } from "../prettier";

const ARROW_HEAD_WIDTH = 7;
const ARROW_HEAD_HEIGHT = 10;
const ARROW_HEAD_HALF_WIDTH = ARROW_HEAD_WIDTH / 2;
const MAX_FONT = 30;
const ABSTRACT_VIEW_TRIGGER_FONT_PX = 5;
const MAX_PARSED_JSON_GRAPH_CACHE_ENTRIES = 8;

interface ParsedJsonGraphCacheEntry {
  eTag: string;
  source: string;
  graphs: JSONGraphs;
}

// TamarinGraph creates abbreviated fact copies, so cached parsed graphs can be
// reused directly without leaking state between renders.
const parsedJsonGraphCache = new Map<string, ParsedJsonGraphCacheEntry>();

type ZoomLevel = "ZoomIn" | "ZoomOut";



export interface ActionText {
  text: string | null;
  bb: DOMRect | null;
  fontSize: string | null;
  fontFamily: string | null;
}

function asEllipse(ellipse: SVGEllipseElement): Ellipse {
  const selection = select(ellipse);
  return {
    c: {
      x: Number(selection.attr("cx")),
      y: Number(selection.attr("cy"))
    },
    rx: Number(selection.attr("rx")),
    ry: Number(selection.attr("ry"))
  }
}

function getActionText(g: SVGGElement): ActionText {
  const actionTextSelection = select<SVGGElement, unknown>(g)
    .selectChildren<SVGTextElement, unknown>("text")
    .filter(function (this) {
      return this.textContent?.startsWith("#") ?? false
    });

  if (actionTextSelection.size() !== 1)
    return {
      text: null,
      bb: null,
      fontSize: null,
      fontFamily: null
    };

  return {
    text: actionTextSelection.nodes()[0].textContent,
    bb: actionTextSelection.nodes()[0].getBBox(),
    fontSize: actionTextSelection.nodes()[0].getAttribute("font-size"),
    fontFamily: actionTextSelection.nodes()[0].getAttribute("font-family"),
  }
}

function getTitleText(g: SVGGElement): string {
  return select<SVGGElement, unknown>(g).selectChild<SVGTitleElement>("title").text();
}

function getSimplificationFromCookie(): number {
  const k = "simplification=";
  const s = document.cookie.indexOf(k);
  // assume simpification level values from 0 to 9 (one digit)
  return s === -1 ? -1 : Number(document.cookie.charAt(s + k.length));
}

function constructJsonSrcParamsFromCookie(): string {
  const param = new URLSearchParams();
  if (document.cookie.indexOf("abbreviate=") === -1) {
    param.append("unabbreviate", "");
  }
  if (document.cookie.indexOf("auto-sources=") === -1) {
    param.append("no-auto-sources", "");
  }
  const smpl = getSimplificationFromCookie();

  if (smpl !== -1) {
    if (smpl === 0) {
      param.append("uncompact", "");
      param.append("uncompress", "");
    }
    param.append("simplification", smpl.toString());
  }

  return param.toString();
}






/** A dictionary where uses zoom level as key 
 * and the raw <g> element that contains how the object should be rendered on screen as value */
type MinimizableObject = { [key in ZoomLevel]: SVGGElement | null };

export class DotGraphViz extends HTMLElement {

  /** The source URL of the dot graph definition 
   * 
   * Passed in as attribute `dotsrc`  which can be either:
   * - A path to the dot file in the public folder during development
   * - A location that serves the dot file during production */
  jsonSrc?: string | null;

  jsonSrcParams?: string;
  checkJsonSrcParamChangeInterval?: number;

  json?: VizGraph;
  graph?: DiGraph;
  /** Root <svg> element */
  svg?: SVGSVGElement;
  /** The direct descendant <g> element of <svg> element, container of the whole graph*/
  svgg?: SVGGElement | null;

  initTransform?: string;
  zoomLevel: ZoomLevel = "ZoomIn"; // the graph always starts with most detailed zoom

  isAbstractEnabled: boolean = false; // Abstract node content toggle

  // here stores nodes and edges that should be rendered based on current zoom level
  minimizableObjects: {
    edges: { [key: string]: MinimizableObject },
    nodes: { [key: string]: MinimizableObject }
  } = {
      edges: {},
      nodes: {}
    }

  highlightConnections: DiGraphConnections | null = {
    nodes: [],
    edges: []
  }

  resizeObserver?: ResizeObserver;
  isAbbreviationEnabled = false;


  constructor() {
    super();
  }

  connectedCallback() {
    this.isAbstractEnabled = document.cookie.indexOf('abstract') !== -1;
    this.jsonSrc = this.getAttribute("dotsrc");
    this.isAbbreviationEnabled = document.cookie.indexOf("abbreviate") !== -1;

    if (!this.jsonSrc || !this.jsonSrc.trim().length) {
      console.error("[dot-graph-viz]: No dot graph source url provided.");
      return;
    }

    if (import.meta.env.PROD) {
      // for production, parameters are read from cookies and attached to the json source url 
      const newJsonSrc = this.jsonSrc.split("?").shift(); // element before ?
      this.jsonSrcParams = constructJsonSrcParamsFromCookie();
      // TODO: need to handle invalid json source url better
      // since source url is manipulated here and another check should be inplace, the check above is kind of redundant
      this.jsonSrc = newJsonSrc!.concat("?").concat(this.jsonSrcParams);
    }

    this.resizeObserver = new ResizeObserver(entries => {
      for (const _ of entries) {
        this.handleAbstractionLevel();
      }
    });

    this.resizeObserver.observe(this);

    this.fetchJsonSource(this.jsonSrc)
      .then((json) => {
        this.renderJson(json);
      }).catch(err => {
        console.error("[dot-graph-viz]: Error occurs during fetch\n", err);
      });
  }

  disconnectedCallback() {
    this.resizeObserver?.disconnect();
  }

  // Render the graph using JSON string
  renderJson = (jsonGraphs: JSONGraphs) => {

    for (const jsonGraph of jsonGraphs.graphs) {
      const ctx = new TamarinGraphBuildContext(this.isAbbreviationEnabled ? jsonGraph.jgAbbrevs : []);
      const simplificationValue = getSimplificationFromCookie();

      const tgraph = new TamarinGraph(jsonGraph, ctx, simplificationValue === -1 ? 2 : simplificationValue);
      this.render(tgraph.dot()).then(() => {
        if (this.isAbbreviationEnabled) {
          this.renderLegend(ctx);
        }
      });

    }


  }

  /**
  * Render legend box as a table on right bottom corner
  * @remark
  * If user click on the table row, it will highlight the clicked row and unhighlight the others.
  * 
  * Clicking on the other place of the document will unhighlight all row.
  * 
  */
  renderLegend = (ctx: TamarinGraphBuildContext) => {
    if (ctx.abbreviations.length > 0) {
      const lcontainer = document.createElement("div");
      lcontainer.setAttribute("class", "lgd-container");
      const ltable = document.createElement("table");
      lcontainer.appendChild(ltable);
      
      // clear all selection lambda
      const clearSelection = () => {
        for (const r of ltable.children) {
          r.setAttribute("class", "lgd-item");
        }
      }
      ctx.abbreviations.forEach((abbrev, index) => {
        const legend = document.createElement("tr");
        legend.setAttribute("class", "lgd-item");

        const highlightNodes = () => {
          this.highlightConnections = { nodes: Array.from(ctx.abbrevMap[index]?.values() ?? []).map(id => id.slice(4)), edges: [] };
          this.highlight();
        }

        // toggle highlight when user click on legend row
        legend.addEventListener("click", function () {
          // legend label highlight
          if (this.classList.contains("active")) {
            this.setAttribute("class", "lgd-item");
          }
          else {
            clearSelection();
            this.setAttribute("class", "lgd-item active");
          }

          // node highlight
          highlightNodes();

        });

        // the three columns of the legend row
        // the abbreviation
        const legendAbbrev = document.createElement("td");
        legendAbbrev.textContent = prettierJSONGraphNodeTerm(abbrev.jgaAbbrev);
        legend.appendChild(legendAbbrev);

        // the equal sign
        const legendEq = document.createElement("td");
        legendEq.textContent = "=";
        legend.appendChild(legendEq);

        // the expansion of the abbreviation
        const legendExpand = document.createElement("td");
        legendExpand.textContent = prettierJSONGraphNodeTerm(abbrev.jgaExpansion);
        legend.appendChild(legendExpand);

        ltable.appendChild(legend);
      });

      this.appendChild(lcontainer);
      document.addEventListener("click", (ev) => {
        if (ev.target instanceof Element && ev.target.tagName !== "TD" && ev.target.tagName !== "TR" && !ev.target.closest(this.getNodeSelector())) {
          // clear legend highlight when clicking on other places on the document than <td> or <tr>
          clearSelection();
          this.clearHighlight();
          this.highlightConnections = null;
        }
      })
    }
  }

  /** Render the graph as SVG given dot graph definition
   * 
   * @param dotString The dot graph definition (usually saved as a `*.dot` file and start with "digraph" in our case)
   */
  render = (dotString: string | DotGraph) => new Promise<void>((resolve, reject) => {
    if (this.checkJsonSrcParamChangeInterval !== undefined) {
      clearInterval(this.checkJsonSrcParamChangeInterval);
    }
    instance().then(viz => {
      /* Resetting all the components */
      this.innerHTML = "";
      this.svg = undefined;
      this.svgg = null;
      this.highlightConnections = { nodes: [], edges: [] };
      this.minimizableObjects = {
        edges: {},
        nodes: {}
      };

      this.svg = viz.renderSVGElement(dotString);
      this.json = viz.renderJSON(dotString) as VizGraph;
      this.graph = new DiGraph(this.json, this.svg);

      // attach SVG to DOM
      this.append(this.svg);

      // Allow selecting/copying text elements with the mouse
      selectAll<SVGTextElement, unknown>("text")
        .on("mousedown", function (event) {
          event.stopPropagation();
        })
        .filter(function() { return !(this as SVGTextElement).closest("g.node"); })
        .style("cursor", "text")

      this.svgg = select(this.svg).selectChild<SVGGElement>("g").node();

      // extract and compute zoom level dependent shape for minimizable objects
      this.constructMinimizableObjects();

      // get initial translation transform
      const translate = this.svgg?.transform.baseVal.getItem(2);
      if (!translate || translate.type !== SVGTransform.SVG_TRANSFORM_TRANSLATE) {
        throw Error("Second Initial Transform on graph is not Translation");
      }
      this.initTransform = `translate(${translate.matrix.e} ${translate.matrix.f})`;

      // create zoom behavior
      const zoomBehavior = zoom<SVGSVGElement, unknown>().scaleExtent([0, Infinity]).on("zoom", this.handleZoom)
      // register zoom behavior
      select(this.svg).call(zoomBehavior);

      this.handleAbstractionLevel();

      // register onclick highlight event
      for (const node of Object.values(this.graph.nodes)) {
        select(this.svgg).selectChild("#" + node.elementId)
          .classed("clickable", true).on("click", this.handleNodeClick)
      }

      // register clear highlight event
      this.svg?.addEventListener("click", (event: MouseEvent) => {
        const target = event.target as HTMLElement;
        // only clear when click on area that is not a node
        if (!target.closest(this.getNodeSelector()) && !target.closest("text.abbrev")) {
          this.clearHighlight();
          this.highlightConnections = null;
          window.getSelection()?.removeAllRanges();
        }
      });

      if (!this.checkJsonSrcParamChangeInterval) {
        this.checkJsonSrcParamChangeInterval = setInterval(() => {
          const params = constructJsonSrcParamsFromCookie();
          if (this.jsonSrcParams && params !== this.jsonSrcParams) {
            this.jsonSrc = this.getAttribute("dotsrc");
            this.jsonSrc = this.jsonSrc?.split("?").shift(); // element before ?
            this.jsonSrcParams = params;
            this.jsonSrc = this.jsonSrc?.concat("?").concat(this.jsonSrcParams);
            if (!this.jsonSrc || !this.jsonSrc.trim().length) {
              console.error("[dot-graph-viz]: No dot graph source url provided.");
              return;
            }

            this.fetchJsonSource(this.jsonSrc)
              .then((json) => {
                this.renderJson(json);
              }).catch(err => {
                console.error("[dot-graph-viz]: Error occurs during fetch\n", err);
              });
          }
        }, 1000);
      }

      resolve();

    })
      .catch(reject);
  });


  /*
    Fetches and parses the graph JSON.

    An ETag identifies a response version. When a request returns a version
    already parsed in this page, reuse its parsed representation rather than
    reading and parsing the body again. If the server does not provide an ETag,
    compare the response text to the cached source before deciding whether to
    parse it again.
  */
  fetchJsonSource = async (url: string): Promise<JSONGraphs> => {
    const res = await fetch(url);
    if (!res.ok) {
      throw new Error("Failed to fetch graph json source.");
    }

    const eTag = res.headers.get("ETag");
    const cached = parsedJsonGraphCache.get(url);
    if (eTag !== null && cached?.eTag === eTag) {
      // Refresh the insertion order to keep the cache least-recently-used.
      parsedJsonGraphCache.delete(url);
      parsedJsonGraphCache.set(url, cached);
      return cached.graphs;
    }

    const source = await res.text();
    if (cached?.source === source) {
      // The graph did not change, despite the missing or updated ETag.
      cached.eTag = eTag ?? "";
      parsedJsonGraphCache.delete(url);
      parsedJsonGraphCache.set(url, cached);
      return cached.graphs;
    }

    let graphs: JSONGraphs;
    try {
      graphs = JSON.parse(source) as JSONGraphs;
    } catch {
      throw new Error("Graph source response is not a JSON");
    }

    parsedJsonGraphCache.set(url, {
      eTag: eTag ?? "",
      source,
      graphs
    });
    if (parsedJsonGraphCache.size > MAX_PARSED_JSON_GRAPH_CACHE_ENTRIES) {
      parsedJsonGraphCache.delete(parsedJsonGraphCache.keys().next().value!);
    }

    return graphs;
  };

  constructMinimizableObjects = () => {
    if (!this.graph || !this.svgg)
      return;

    // minimizable nodes
    for (const [nodeId, node] of Object.entries(this.graph.nodes)) {
      if (node.minimizable) {
        const nodeEl = select(this.svgg).selectChild<SVGGElement>("#" + node.elementId).node();
        if (nodeEl) {
          this.minimizableObjects.nodes[nodeId] = {
            "ZoomIn": null,
            "ZoomOut": null
          }
          this.minimizableObjects.nodes[nodeId]["ZoomIn"] = nodeEl;
          select(nodeEl).classed("clickable", true).on("click", this.handleNodeClick);
          this.minimizableObjects.nodes[nodeId]["ZoomOut"] = this.minimizeNode(nodeEl);
        }
      }
    }
    // minimizable edges
  };

  minimizeNode = (g: SVGGElement): SVGGElement => {
    const center = calculateCentroid(g.getBBox());
    const actionText = getActionText(g);

    const minimized = create<SVGGElement>("svg:g")
      .attr("id", g.getAttribute("id"))
      .attr("class", "node clickable mini")
      .on("click", this.handleNodeClick);

    minimized.append("title")
      .text(getTitleText(g));

    const polygon = select(g).selectChild<SVGPolygonElement>("polygon");
    const polygonBBox = polygon.node()!.getBBox();

    minimized.append("polygon")
      .attr("points", polygon.attr("points"))
      .attr("fill", polygon.attr("fill"))
      .attr("stroke", polygon.attr("stroke"));

    // Shorten action text
    const actualText = actionText.text ?
      actionText.text.indexOf("[") >= 0 ?
        actionText.text.slice(0, actionText.text.indexOf("[")) + ""
        : actionText.text
      : "default";

    minimized.append("text")
      .attr("x", center.x)
      .attr("y", center.y)
      .attr("text-anchor", "middle")
      .attr("alignment-baseline", "middle")
      .attr("font-family", actionText.fontFamily) // *WARNING, hard-coded, pls adapt it to record font family
      .attr("font-size", `${Math.min(MAX_FONT, Math.min(polygonBBox.width / actualText.length / 0.54, polygonBBox.height * 0.8)).toFixed(0)}px`)
      .text(actualText);

    return minimized.node()!; // I just created it so its node() must be non-null
  };

  minimizeEdge = (g: SVGGElement, fromNode: SVGGElement | null, toNode: SVGGElement | null): SVGGElement => {
    const oldEdge = select(g);
    const oldEdgePath = oldEdge.selectChild<SVGPathElement>("path");
    const oldEdgePolygon = oldEdge.selectChild<SVGPathElement>("polygon");
    const edgeStrokeWidth = oldEdgePolygon.attr("stroke-width") === null ? 1 : Number(oldEdgePolygon.attr("stroke-width"));
    const arrowHeadTipOffset = Math.sqrt(ARROW_HEAD_HALF_WIDTH * ARROW_HEAD_HALF_WIDTH + ARROW_HEAD_HEIGHT * ARROW_HEAD_HEIGHT) / ARROW_HEAD_HALF_WIDTH * (edgeStrokeWidth / 2);
    const arrowHeadRealHeight = ARROW_HEAD_HEIGHT + arrowHeadTipOffset + edgeStrokeWidth / 2;

    const minimized = create<SVGGElement>("svg:g")
      .attr("id", oldEdge.attr("id"))
      .attr("class", "edge mini");

    minimized.append("title"); // need to be completed with same title as the old one

    let edgePath: string = oldEdgePath.attr("d");
    const oldCurve = getCubicBezierCurve(edgePath);
    const [oldTailGrad, oldHeadGrad] = getCubicBezierCurveGradients(oldCurve);

    // let isTailReprojected = false;

    if (fromNode) {
      // the node where the edge starts from
      const fromEllipse = asEllipse(select(fromNode)
        .selectChild<SVGEllipseElement>("ellipse").node()!); // WARNING* ! used

      // start from the starting point of the curve and in direction of the negative gradient
      // opposite of the (arrow) path's direction
      const tailRay: Ray = {
        o: oldCurve.start,
        d: inv(oldTailGrad)
      };

      // intersection to the from-ellipse by extending the tail ray
      const tailIts = intersect(tailRay, fromEllipse);

      if (tailIts) {
        edgePath = extendCurvePath(edgePath, traverse(tailRay, tailIts));
      }
      else {
        // isTailReprojected = true;
        const tailProj = project(oldCurve.start, fromEllipse);
        edgePath = extendCurvePath(edgePath, tailProj);
      }
    }

    if (toNode) {
      // the node where the edge ends at
      const toEllipse = asEllipse(select(toNode)
        .selectChild<SVGEllipseElement>("ellipse").node()!);

      const headRay: Ray = {
        o: oldCurve.end,
        d: oldHeadGrad
      };

      const headIts = intersect(headRay, toEllipse);
      let headItsPoint: Vec2;
      let headDirection: Vec2;
      if (headIts) {
        // has to consider the offset of the arrow head
        edgePath = extendCurvePath(edgePath, undefined, traverse(headRay, headIts - arrowHeadRealHeight));
        headItsPoint = traverse(headRay, headIts);
        headDirection = inv(headRay.d);
      }
      else {
        const headProj = project(oldCurve.end, toEllipse);
        headItsPoint = headProj;
        // from the projection point to the old curve end
        const projHeadRay: Ray = {
          o: headProj,
          d: direction(headProj, oldCurve.end)
        }
        headDirection = projHeadRay.d;
        edgePath = extendCurvePath(edgePath, undefined, traverse(projHeadRay, arrowHeadRealHeight));

        // if (isTailReprojected) {
        //   throw new Error("Not implemented yet")
        // } else {
        // const projHeadRay: Ray = {
        //   o: headProj,
        //   d: direction(headProj, oldCurve.start)
        // }
        //   edgePath = `M${print2f(oldCurve.start)}L${print2f(traverse(projHeadRay, arrowHeadRealHeight))}`;
        //   headDirection = projHeadRay.d;
        // }

      }
      // add new arrow head

      // We obtain the angle between the end segment and vector (0, -1) (since SVG's rotation transform is defined as an angle of the angle from direction (0, -1) in clockwise manner) by taking the dot product of the inverse of the end ray's direction and vector (0, -1). The inversion (-endRay.d) is because we want the end segment's direction to point out so that it is comparable with the vector (0, -1) which is also pointing out. Math.acos(x) gives the result in radian so we have to convert it back to degree. Finally, the angle we calculated needed to be inverted (counter-clockwise) 

      const rotation = (cross({ x: 0, y: -1 }, headDirection) > 0 ? 1 : -1) * Math.acos(dot(headDirection, { x: 0, y: -1 })) * 180 / Math.PI;
      /**
      * Arrow Head Creation
      * Arrow heads created by graphviz have a width of 7 and a height of 10.
      * After edge re-route i.e. the start and end points get extended to their from and to-nodes respectively, the arrow heads (which are typically at the end points of the edges) must be re-created as well.
      * The arrow head triangle is first created as an upside down triangle with the tip pointing down and the base paralleling with the x-axis i.e. as ▼
      * The arrow head is then rotated to be aligned with the end point's gradient direction i.e. to be aligned with the last / end segment of the edge.
      */
      const arrowHeadTipPoint = sub(headItsPoint, { x: 0, y: arrowHeadTipOffset });
      const arrowHeadRightPoint = sub(arrowHeadTipPoint, { x: -ARROW_HEAD_HALF_WIDTH, y: ARROW_HEAD_HEIGHT });
      const arrowHeadLeftPoint = sub(arrowHeadTipPoint, { x: ARROW_HEAD_HALF_WIDTH, y: ARROW_HEAD_HEIGHT });
      minimized.append("path")
        .attr("d", `M${print2f(arrowHeadLeftPoint)}L${print2f(arrowHeadTipPoint)}L${print2f(arrowHeadRightPoint)}Z`)
        .attr("fill", oldEdgePolygon.attr("fill"))
        .attr("stroke", oldEdgePolygon.attr("stroke"))
        .attr("stroke-width", oldEdgePolygon.attr("stroke-width"))
        .attr("transform", `rotate(${rotation},${print2f(headItsPoint)})`);
    }
    else {
      // keep the old arrow head
      minimized.append("polygon")
        .attr("points", oldEdgePolygon.attr("points"))
        .attr("fill", oldEdgePolygon.attr("fill"))
        .attr("stroke", oldEdgePolygon.attr("stroke"))
        .attr("stroke-width", oldEdgePolygon.attr("stroke-width"));
    }

    minimized.append("path")
      .attr("d", edgePath)
      .attr("fill", oldEdgePath.attr("fill"))
      .attr("stroke", oldEdgePath.attr("stroke"))
      .attr("stroke-width", oldEdgePath.attr("stroke-width"))
      .attr("stroke-dasharray", oldEdgePath.attr("stroke-dasharray"));

    return minimized.node()!; // I just created it so its node() must be non-null
  }

  /*
    Responsible for handling zoom events for the graph
  */
  handleZoom = (event: D3ZoomEvent<SVGSVGElement, unknown>) => {
    if (!this.svgg)
      return;

    // scale the graph: attach the zoom transform after the initial translation
    select(this.svgg).attr("transform", event.transform.toString() + " " + this.initTransform);
     this.handleAbstractionLevel();
  };

  handleAbstractionLevel = () => {
    if (!this.isAbstractEnabled || !this.svgg || !this.svgg.getCTM())
      return;

    // screen_font_size = scale_zoom * scale_viewport * svg_font_size (default = 8px)
    // Note that here getCTM().a (which equals to getCTM().d) gives scale_zoom * scale_viewport due to forced uniform scaling
    // see https://developer.mozilla.org/en-US/docs/Web/SVG/Reference/Attribute/preserveAspectRatio
    const screen_fs = (this.svgg.getCTM()!).a * 8;

    // Keep detailed node rendering until nodes are much smaller on screen.
    const zoomLevel = screen_fs >= ABSTRACT_VIEW_TRIGGER_FONT_PX ? "ZoomIn" : "ZoomOut";

    // do nothing when zoom level didn't change
    if (zoomLevel === this.zoomLevel)
      return;

    // zoom level changed
    const prevZoomLevel = this.zoomLevel;
    this.zoomLevel = zoomLevel;

    for (const [_, edge] of Object.entries(this.minimizableObjects.edges)) {
      // remove minimizable objects rendered as the previous zoom level

      if (prevZoomLevel) {
        select(edge[prevZoomLevel]).remove();
      }
      // add minimizable objects for the current zoom level
      if (edge[zoomLevel]) {
        this.svgg.appendChild(edge[zoomLevel]);
      }
    }

    for (const [_, node] of Object.entries(this.minimizableObjects.nodes)) {
      // remove minimizable objects rendered as the previous zoom level

      if (prevZoomLevel) {
        select(node[prevZoomLevel]).remove();
      }
      // add minimizable objects for the current zoom level
      if (node[zoomLevel]) {
        this.svgg.appendChild(node[zoomLevel]);
      }
    }

    // keep highlight state
    this.highlight();
  }

  /*
    When a node is clicked, all the downward connections (including the edges) of the node are highlighted.
  */
  handleNodeClick = (event: MouseEvent) => {
    if (!this.graph)
      return;

    const nodeElementId = select(event.currentTarget as HTMLElement).attr("id");
    this.highlightConnections = this.graph.getConnections(this.graph.reverseLookup.nodes[nodeElementId]);

    this.highlight();
  };

  highlight = () => {
        if (!this.graph || !this.svgg || !this.highlightConnections || (this.highlightConnections.nodes.length === 0 && this.highlightConnections.edges.length === 0))
      return;

    // clear highlight
    this.clearHighlight();

    // add new highlight
    select(this.svgg).classed("highlighted", true);

    for (const nodeId of this.highlightConnections.nodes) {
      select(this.svgg).selectChild("#" + this.graph.nodes[nodeId].elementId)
        .classed("active", true);
    }

    for (const edgeId of this.highlightConnections.edges) {
      select(this.svgg).selectChild("#" + this.graph.edges[edgeId].elementId)
        .classed("active", true);
    }
  }

  /*
    Clear the highlighted edges and nodes of the graph
  */
  clearHighlight = () => {
    if (!this.svgg)
      return;

    const g = select(this.svgg).classed("highlighted", false);

    g.selectChildren("g.active")
      .classed("active", false);
  };

  getNodeSelector = () => {
    return Object.values(this.graph?.nodes ?? {}).map(n => "#" + n.elementId).join(",");
  }
}

customElements.define("dot-graph-viz", DotGraphViz);