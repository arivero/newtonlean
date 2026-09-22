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

## Working hypothesis: what difficulties might Newton have recognized?

**Educated guess, not an established account of Newton's intentions.** Our
best-supported reading is that he recognized restrictions and ambiguities in
passing between geometric approximations and force-generated motion. The
sources inspected do not establish that he discovered an internal contradiction
in his mechanics. The following ranking separates textual evidence from our
reconstruction; it adds no historical proof-dependency edge.

1. **Quadratic contact needs restricted geometry — strong textual evidence.**
   The 1687 Lemma XI scholium explicitly discusses departures of different
   orders and restricts the curvature; 1713 puts a curvature condition in the
   lemma's statement. Thus Newton demonstrably recognized the danger of
   applying a quadratic comparison beyond its permitted contact geometry.
   This qualification already exists in 1687, so it is not evidence of a
   contradiction first discovered between editions.
   Sources: [1687, NATP00077 par39](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par39),
   [1713, NATP00082 par36](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par36).

2. **Different measures of departure need a justified correspondence — plausible
   interpretation of the revisions.** The later organization of Proposition VI
   emphasizes a sagitta route, but retains Lemma X as an alternative. It is
   plausible that Newton wanted to secure or clarify the relation between
   generated displacement and geometric departure. Our matched-duration
   constant-force calculation shows why their calibration matters; it does
   not demonstrate that Newton made that numerical error or abandoned the
   earlier argument. Proposition VI is supporting comparison material, outside
   the primary I–IV target.
   Sources: [1713, NATP00082 par89–90](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par89),
   [edition-local comparison](research/edition-comparison.md),
   [checked special case](research/M4.md#checked-route-comparison).

3. **Approximating a given curve and constructing a motion are different
   obligations — our leading research conjecture, weak evidence about Newton's
   own diagnosis.** Lemmas II–III begin with geometric figures; Proposition I
   invokes Lemma III corollary 4 when passing from impulsive polygons to
   uninterrupted action. Our question is whether the permitted premises also
   secure a coherent time-to-position map for the constructed polygons.
   The inspected passages do not document Newton identifying this as an
   existence gap. Their retention in 1713 also prevents treating the later
   revisions as evidence that he explicitly repaired it.
   Sources: [1687, NATP00077 par3–10](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par3),
   [1687 Proposition I, par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45),
   [1713 Proposition I, par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51).

Our new finite result constrains this conjecture. Under our stated constant-force
impulse schedule, subdivision changes endpoints, but the exact position
residual is `(Σ d_i²/2)*a`, with coefficient bounded by half the largest cell
duration times elapsed time. This provides a classical route toward controlling
the mismatch, not evidence of an irreparable inconsistency. Convergence and
general central-force realization remain unproved.
See [the constructed partition comparison](research/PARTITION_CONTROL.md).

**Prioritized discriminator: zero force.** We will derive uniform rectilinear
motion, exact subdivision independence and finite joining from the recurrence,
including rest. Collinear paths can have zero geometric defect while different
time parametrizations describe different motions; therefore zero area defect
alone is insufficient identifying data. A difficulty here would first require
checking our kinematic definitions and premises, not attributing an error to
Newton. Success would isolate which further obligations enter with nonzero
force. No result so far establishes a universal nonzero action constant.

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
