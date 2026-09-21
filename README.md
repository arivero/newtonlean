# Formal Genealogy of Newton's Limit Dynamics

This project reconstructs the changing dependency graph from Newton's *De motu*
(1684) through the *Principia* (1687, proposed 1694 revisions, 1713 and selected
1726 changes), and formalizes the mathematical content in Lean 4.

The first milestone, M1, is deliberately narrow: track the logical status of
the quadratic initial deflection `s ∝ t^2`. Historical statements, modern
consequences, and editorial reconstructions remain separate.

See [`research/STATE.md`](research/STATE.md), [`research/sources.md`](research/sources.md),
and [`research/dependency-schema.yaml`](research/dependency-schema.yaml).

Current result: [M1 evidence and proof boundary](research/M1.md),
[primary passages](research/passages.md), and [generated graphs](research/graphs.md).
M1 remains open: the compiled enclosure reconstruction is conditional on
the geometric limits and mechanical area identification.

Build with `lake build` (Lean 4.19.0, core only, no external packages).
Validate source-linked graphs with `python3 scripts/check_graph.py`.
Re-extract marked primary passages with `python3 scripts/catalogue_m1.py`.
No post-Newtonian theorem is used to bridge historical gaps.
