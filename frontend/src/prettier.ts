import { isJSONGraphNodeTermConst, isJSONGraphNodeTermFunct, JSONGraphNodeFact, JSONGraphNodeTerm } from "./jsongraph";

// Line width used when rendering. The Haskell backend uses ~130 (inflated by 1.3× font
// compensation for proportional fonts). 80 is more readable for graph node labels.
const LINE_WIDTH = 80;

// -----------------------------------------------------------------------------
// Hughes-PJ Doc type — iterative implementation
//
// The original recursive implementation (concat walking the spine, nestDoc/flatten
// traversing the tree) caused SIGILL (JS stack overflow) on large graphs with
// ~3000 terms. Fix: Concat and Nest are O(1) structural nodes; best(), fits(),
// flatten() and renderDoc() use explicit stacks instead of recursion.
// -----------------------------------------------------------------------------

type Doc =
    | { tag: 'Empty' }
    | { tag: 'Text';   s: string }
    | { tag: 'Line' }                         // newline; indent resolved by surrounding Nest
    | { tag: 'Concat'; a: Doc; b: Doc }       // O(1) concatenation
    | { tag: 'Nest';   n: number; d: Doc }    // increase indent by n
    | { tag: 'Union';  flat: Doc; full: Doc }; // try flat (no Lines) first, else full

const docEmpty: Doc = { tag: 'Empty' };
const docLine:  Doc = { tag: 'Line' };

function text(s: string): Doc {
    return s === "" ? docEmpty : { tag: 'Text', s };
}

// O(1) — just wraps in a Concat node, no traversal.
function concat(a: Doc, b: Doc): Doc {
    if (a.tag === 'Empty') return b;
    if (b.tag === 'Empty') return a;
    return { tag: 'Concat', a, b };
}

// O(1) — just wraps in a Nest node, no traversal.
function nest(n: number, d: Doc): Doc {
    return n === 0 ? d : { tag: 'Nest', n, d };
}

// Replace every Line with a space (builds the flat variant of d).
// Iterative to avoid stack overflow on deep Concat trees.
function flatten(d: Doc): Doc {
    const stack: Doc[] = [d];
    const parts: Doc[] = [];
    while (stack.length > 0) {
        const cur = stack.pop()!;
        switch (cur.tag) {
            case 'Empty':  break;
            case 'Text':   parts.push(cur); break;
            case 'Line':   parts.push(text(' ')); break;
            case 'Concat': stack.push(cur.b); stack.push(cur.a); break;
            case 'Nest':   stack.push(cur.d); break;
            case 'Union':  stack.push(cur.flat); break;
        }
    }
    if (parts.length === 0) return docEmpty;
    return parts.reduceRight<Doc>((b, a) => ({ tag: 'Concat', a, b }), docEmpty);
}

// Try flat layout first, fall back to full. `flat` must contain no Line nodes.
function group(d: Doc): Doc {
    return { tag: 'Union', flat: flatten(d), full: d };
}

// Check whether the first line of `d` fits within `n` remaining columns.
// Iterative to avoid stack overflow.
function fits(n: number, d: Doc): boolean {
    const stack: Doc[] = [d];
    let rem = n;
    while (stack.length > 0) {
        if (rem < 0) return false;
        const cur = stack.pop()!;
        switch (cur.tag) {
            case 'Empty':  break;
            case 'Line':   return true;   // first line ends here — it fits
            case 'Text':   rem -= cur.s.length; break;
            case 'Concat': stack.push(cur.b); stack.push(cur.a); break;
            case 'Nest':   stack.push(cur.d); break;
            case 'Union':  stack.push(cur.flat); break;
        }
    }
    return rem >= 0;
}

// Render a Doc to a string using an explicit stack (no recursion).
function renderDoc(width: number, d: Doc): string {
    type Frame = { indent: number; doc: Doc };
    const stack: Frame[] = [{ indent: 0, doc: d }];
    const out: string[] = [];
    let col = 0;

    while (stack.length > 0) {
        const { indent, doc } = stack.pop()!;
        switch (doc.tag) {
            case 'Empty': break;
            case 'Text':
                out.push(doc.s);
                col += doc.s.length;
                break;
            case 'Line':
                out.push('\\l' + '\\ '.repeat(indent));
                col = indent;
                break;
            case 'Concat':
                stack.push({ indent, doc: doc.b });
                stack.push({ indent, doc: doc.a });
                break;
            case 'Nest':
                stack.push({ indent: indent + doc.n, doc: doc.d });
                break;
            case 'Union':
                stack.push({ indent, doc: fits(width - col, doc.flat) ? doc.flat : doc.full });
                break;
        }
    }
    return out.join('');
}
function renderDocTerm(width: number, d: Doc): string {
    type Frame = { indent: number; doc: Doc };
    const stack: Frame[] = [{ indent: 0, doc: d }];
    const out: string[] = [];
    let col = 0;

    while (stack.length > 0) {
        const { indent, doc } = stack.pop()!;
        switch (doc.tag) {
            case 'Empty':
                break;

            case 'Text':
                out.push(doc.s);
                col += doc.s.length;
                break;

            case 'Line':
                out.push("\n" + " ".repeat(indent)); // replaced //l with \n for term rendering
                col = indent;
                break;

            case 'Concat':
                stack.push({ indent, doc: doc.b });
                stack.push({ indent, doc: doc.a });
                break;

            case 'Nest':
                stack.push({ indent: indent + doc.n, doc: doc.d });
                break;

            case 'Union':
                stack.push({
                    indent,
                    doc: fits(width - col, doc.flat) ? doc.flat : doc.full
                });
                break;
        }
    }

    return out.join("");
}

// -----------------------------------------------------------------------------
// Combinators
// -----------------------------------------------------------------------------

function beside(a: Doc, b: Doc): Doc {
    return concat(a, concat(text(' '), b));
}

function vcat(ds: Doc[]): Doc {
    if (ds.length === 0) return docEmpty;
    return ds.reduce((acc, d) => concat(acc, concat(docLine, d)));
}

// sep: all on one line (hsep), else each on its own line (vcat).
function sep(ds: Doc[]): Doc {
    return group(vcat(ds));
}

// fsep: fill-separated — pack items left-to-right, wrap when full.
// Right-to-left iterative fold so fsep([t1..tN]) never grows the call stack.
function fsep(ds: Doc[]): Doc {
    if (ds.length === 0) return docEmpty;
    let result = ds[ds.length - 1];
    for (let i = ds.length - 2; i >= 0; i--) {
        const head = ds[i];
        result = { tag: 'Union',
                   flat: beside(head, result),
                   full: concat(head, concat(docLine, result)) };
    }
    return result;
}

// fcat: fill-concatenated — same as fsep but no spaces between items.
// Right-to-left iterative fold for the same reason.
function fcat(ds: Doc[]): Doc {
    if (ds.length === 0) return docEmpty;
    let result = ds[ds.length - 1];
    for (let i = ds.length - 2; i >= 0; i--) {
        const head = ds[i];
        result = { tag: 'Union',
                   flat: concat(head, result),
                   full: concat(head, concat(docLine, result)) };
    }
    return result;
}

// Append `p` after each element except the last. Matches Haskell's `punctuate`.
function punctuate(p: Doc, ds: Doc[]): Doc[] {
    if (ds.length <= 1) return ds;
    return ds.map((d, i) => i < ds.length - 1 ? concat(d, p) : d);
}

// nestShort' lead finish body — indent body by length(lead)+1.
// Matches Haskell's nestShort / nestShort' in Text/PrettyPrint/Class.hs.
function nestShortStr(lead: string, finish: string, body: Doc): Doc {
    const n = lead.length + 1;
    return sep([concat(text(lead), nest(n, body)), text(finish)]);
}

// -----------------------------------------------------------------------------
// Tamarin-specific term pretty-printing
// Matches prettyTerm in lib/term/src/Term/Term.hs:268-296
// -----------------------------------------------------------------------------

function flattenPair(t: JSONGraphNodeTerm): JSONGraphNodeTerm[] {
    if (isJSONGraphNodeTermFunct(t) && t.jgnFunct === "pair") {
        return [...flattenPair(t.jgnParams[0]), ...flattenPair(t.jgnParams[1])];
    }
    return [t];
}

// ppTerms sepa n lead finish ts =
//   fcat . (text lead :) . (++[text finish]) . map (nest n) . punctuate (text sepa) . map ppTerm $ ts
function ppTerms(sepa: string, n: number, lead: string, finish: string,
                 ts: JSONGraphNodeTerm[]): Doc {
    const docs = punctuate(text(sepa), ts.map(prettyTerm)).map(d => nest(n, d));
    return fcat([text(lead), ...docs, text(finish)]);
}

// ppFun f ts = text (f++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
// Note: punctuate uses bare "," and fsep's beside() supplies the separating space.
function ppFun(f: string, ts: JSONGraphNodeTerm[]): Doc {
    return concat(
        text(f + "("),
        concat(fsep(punctuate(text(","), ts.map(prettyTerm))), text(")"))
    );
}

function prettyTerm(t: JSONGraphNodeTerm): Doc {
    if (isJSONGraphNodeTermConst(t)) return text(t.jgnConst);

    switch (t.jgnFunct) {
        // FApp (NoEq pairSym) _ → ppTerms ", " 1 "<" ">" (split t)
        case "pair":
            return ppTerms(", ", 1, "<", ">", flattenPair(t));

        // FApp (NoEq expSym) [b,e] → b^e
        case "exp":
            return concat(prettyTerm(t.jgnParams[0]),
                   concat(text("^"), prettyTerm(t.jgnParams[1])));

        // FApp (NoEq natOneSym) [] → %1   (jgnFunct = "tone" from natOneSymString)
        case "tone":
            return text("%1");

        // FApp (NoEq diffSym) [t1,t2] → diff(t1, t2)
        case "diff":
            return ppFun("diff", t.jgnParams);

        // FApp (AC Mult)    ts → ppTerms "*"  1 "(" ")" ts
        case "Mult":    return ppTerms("*",  1, "(", ")", t.jgnParams);
        // FApp (AC Xor)     ts → ppTerms "⊕"  1 "(" ")" ts
        case "Xor":     return ppTerms("⊕",  1, "(", ")", t.jgnParams);
        // FApp (AC Union)   ts → ppTerms "++" 1 "(" ")" ts
        case "Union":   return ppTerms("++", 1, "(", ")", t.jgnParams);
        // FApp (AC NatPlus) ts → ppTerms "%+" 1 "(" ")" ts
        case "NatPlus": return ppTerms("%+", 1, "(", ")", t.jgnParams);

        // FApp (NoEq (f,_)) ts → f(fsep(punctuate comma (map ppTerm ts)))
        default:
            return ppFun(t.jgnFunct, t.jgnParams);
    }
}

// -----------------------------------------------------------------------------
// Tamarin-specific fact pretty-printing
// Matches prettyFact in lib/theory/src/Theory/Model/Fact.hs:537-544
// -----------------------------------------------------------------------------

// ppFact n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppTerm t
// Note: punctuate uses bare "," and fsep's beside() supplies the separating space.
function prettyFact(f: JSONGraphNodeFact): Doc {
    const terms = punctuate(text(","), f.jgnFactTerms.map(prettyTerm));
    return nestShortStr(f.jgnFactName + "(", ")", fsep(terms));
}

// -----------------------------------------------------------------------------
// Public API
// -----------------------------------------------------------------------------

// Render Terms and Facts to correct Graphviz Syntax
export function prettierJSONGraphNodeTerm(t: JSONGraphNodeTerm): string {
    return renderDocTerm(LINE_WIDTH, prettyTerm(t));
}

export function prettierJSONGraphNodeFact(f: JSONGraphNodeFact): string {
    return renderDoc(LINE_WIDTH, prettyFact(f));
}
