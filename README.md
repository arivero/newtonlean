# Newton's changing proof architecture

The [approved goals](research/GOALS.md) target Book I, Section II,
Propositions I–IV in 1687 and 1713 and their De Motu antecedents, with explicit
joining, refinement and trajectory-existence obligations. A universal action
constant is a separate research hypothesis, not a premise of these proofs.
The [three-stage source map](research/SECTION_II.md) records the actual
dependencies; the [obligation queue](research/TASKS.md) separates finite
mechanics, refinement, realization and force identification.

Source-linked reconstructions of quadratic deflection, central-impulse polygons,
contact-area bounds and proposed revisions, with separate De Motu, 1687,
proposed-1694, 1713 and 1726 witnesses. Lean 4.19.0 core/Std only; no mathlib.

The implementation advances all four milestones but **does not certify them
complete**. Geometric, mechanical and manuscript gaps remain explicit in
[research state](research/STATE.md), [M1](research/M1.md), [M2](research/M2.md),
[M3](research/M3.md), and [M4](research/M4.md). Historical results are distinct
from conditional reconstructions and coordinate consistency examples.

Evidence: [passages](research/passages.md), [graphs](research/graphs.md),
[edition comparison](research/edition-comparison.md), and
[formal result ledger](research/formal-results.json).

```sh
lake build
lake build NewtonLimitDynamics
python3 scripts/catalogue_m1.py
python3 scripts/catalogue_formal.py
python3 scripts/collate_sources.py
python3 scripts/check_graph.py
python3 scripts/compare_editions.py
lake env lean research/CheckReferences.lean
git diff --check
```

The historical extraction command name is retained; selections.json now covers
all milestones. `collate_sources.py` checks selected TEI anchors, page/facsimile
metadata, revision tags, and local normalized/diplomatic anchor presence. It is
not a facsimile or palaeographic audit. Graph validation checks local TEI
anchors, source identity, edge metadata and acyclicity. Generated Lean
reference checks inspect actual types and axioms. These checks do not establish
an unproved historical premise.
No post-Newtonian theorem supplies a missing historical construction.

Additional integrity checks:

```sh
python3 scripts/test_evidence_validation.py
sha256sum -c docs/SHA256SUMS
```

See [verification record](research/VERIFICATION.md) for observed results and limits.
