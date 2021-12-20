# Export features

It is possible to export processes defined in .spthy files into the formats
used by other protocol verifiers, making it possible to switch between tools.
One can even translate lemmas in one tool to assumptions in other to combine
these results. The correctness of the translation is proven in [@sapicplus].

The `-m` flag selects an output module:
```
 -m --output-module[=spthy|spthytyped|msr|proverif|deepsec]
``` 

The following outputs are supported:

- *spthy:* parse .spthy file and output
- *spthytyped* - parse and type .spthy file ad output
- *msr* - parse and type .spthy file and translate processes to multiset-rewrite rules
- *proverif*: - translate to [ProVerif](https://bblanche.gitlabpages.inria.fr/proverif/) input format
- *deepsec*: - translate to [Deepsec](https://deepsec-prover.github.io/) input format

## Lemma selection

The same spthy file may be used with multiple tools as backend. To list the
tools that a lemma should be exported to, use the `output` attribute:
```
lemma secrecy[reuse, output=[proverif,msr]]:
```
Lemmas are omitted when the currently selected output module is not in that
list.

## Exporting queries

Security properties are automatically translated, if it is possible. (ProVerif
only supports two quantifier alternations, for example.) As, e.g., DeepSec,
supports queries that are not expressible in Tamarin's language, it is possible
to define blocks that are covered on export. They are written as:
```
export IDENTIFIER:
"
    text to export
"
```
where IDENTIFIER is one of the following:

- `requests`: is included in the requests the target solver tries to prove. E.g.:

    ```
    export requests:
    "
    let sys1 = new sk; (!^3 (new skP; P(sk,skP)) | !^3 S(sk)).

    let sys2 = new sk; ( ( new skP; !^3 P(sk,skP)) | !^3 S(sk)).

    query session_equiv(sys1,sys2).
    "
    ```

## Smart export features

- Some predicates / conditions appear in `if .. ` processes have [dedicates
      translations](007_property-specification.html#sec:predicates-special).

