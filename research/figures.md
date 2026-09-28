# Rendered dependency figures

`scripts/plot_graphs.py` draws the evidence graph of
[dependencies.json](dependencies.json) (validated by `scripts/check_graph.py`)
into `docs/graphs/` as DOT sources plus standalone SVG and, when Pillow is
available, PNG previews.  The figures are a visualization only; the validated
source of truth is `dependencies.json`, and the machine-readable mermaid form
is regenerated into [graphs.md](graphs.md) by `check_graph.py`.

| Figure | Contents |
| --- | --- |
| `docs/graphs/proof-1687` | Proof dependencies inside the 1687 edition (19 nodes, 21 edges) |
| `docs/graphs/proof-1713` | Proof dependencies inside the 1713 edition (25 nodes, 24 edges) |
| `docs/graphs/proof-1726` | Proof dependencies inside the 1726 comparison witness (12 nodes, 8 edges) |
| `docs/graphs/proof-drafts` | De Motu (NATP00089/00090), the Royal-Society reprint and the proposed-1694 ordering |
| `docs/graphs/comparison` | Cross-stage textual comparison and proposed-reordering edges (never proof dependencies) |
| `docs/graphs/section-II` | The transitive closure of everything Section II, Propositions I-IV cites, both editions together |
| `docs/graphs/formalisation-coverage` | The whole evidence graph, every node, green border where a node carries checked Lean results |

Conventions: an arrow runs from the cited result to the result that cites it;
`solid` = explicit dependency, `dashed` = implicit dependency, `dotted` =
editorial interpretation or textual comparison.  Node colour is the witness
stage (De Motu and drafts ochre, 1687 blue, 1713 green, 1726 pink, proposed
1694 amber).  A green border marks a node that has at least one checked Lean
reference attached in `dependencies.json`; grey nodes are historical claims
with no formal backing yet, so the coverage figure shows at a glance which
proofs of the formalisation are mechanized.
