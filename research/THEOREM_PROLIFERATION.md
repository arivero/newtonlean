# Why the theorem inventory is growing

Requested by the user on 5 October 2026, after the acceleration-secant
increment 3f6d359. This is a bounded code/inventory study, not mathematical
recertification or a new historical argument. The handoff and GOALS.md remain
the research targets. Root Sol 6.1 measured the tracked source with the existing
declaration reader and inspected representative proofs; the user separately
requested one sequential GPT-6 Astra architecture review.

## Measured growth

Compare the handoff commit 6a8aa5c with 3f6d359, using
scripts/lean_declarations.py and the unchanged progress_stats.py classifier:

| Inventory | Handoff | Current |
| --- | ---: | ---: |
| Library theorem declarations | 793 | 1,371 |
| Heuristic substantive | 501 | 995 |
| Heuristic arithmetic plumbing | 174 | 195 |
| Heuristic numeric sample | 105 | 155 |
| Heuristic repeated statement | 13 | 26 |
| Definitions and structures | 414 | 631 |
| Library source lines | 10,658 | 19,615 |

The raw change is 579 new theorem names and one removed name, hence +578.
No surviving baseline theorem statement changed. The removal was the unused
HarmonicAccumulation.stateSub_chain. Of the additions, 348 are now in BarrowLib
and 231 in NewtonLimitDynamics; moving an existing declaration does not count
as adding one. There are currently 565 Barrow theorems and 806 Newton theorems.
The inventory includes 141 private supporting theorem declarations. The
current reference harness emits 1,231 checks; those are a different inventory.

560 additions are assigned to Proposition I by the existing module grouping;
the remaining 19 go to shared/stage support, finite work and action diagnostics.
The largest new modules are FiniteEstimates (40), TimeCalibration (37),
HarmonicIntegerSubdivision (37), FiniteAccumulation (34), GeneralForceEndpoint
(22), BoundedCuts (21) and ForceClasses (21). The source graph stayed at
77 nodes, 68 edges and 249 passages. These additions mostly extend the modern
construction beneath the existing historical maps.

The committed history CSV and scripts/progress_stats.py reproduce the raw
snapshot counts. The root's detailed comparison is in
/tmp/newton-theorem-proliferation-2026-10-05.json, including per-module additions,
statement comparison and named counting examples. A textual scan found 98
new direct qualified proof applications and eight new rfl identities. These
are syntax observations, not 98 certified duplicates or a measure of proof
difficulty; a direct application can be a useful specialization. Seven of the
eight rfl identities are classified as substantive.

## Causes and actual costs

Lean core supplies neither this rational geometry nor the completion library.
The project therefore builds finite map estimates, rational order/exhaustion,
Cauchy names, representative independence, quotient operators, closed radius
bounds, binary-time addresses, finite square covers and scalar content. A
single completed operator typically needs a finite comparison, a Cauchy proof,
name-equivalence transport, the quotient lift, compatibility facts and a bound
on completed values. For example, SampledValues builds the completed map from
ordered finite comparisons; its force and acceleration clients use that same
construction. Those supporting statements are real work, although they do not
each discharge a separate Proposition I obligation.

Fractions retain raw numerator/positive-denominator representatives. Value
equality uses Fraction.equiv rather than structure equality. This makes
represented-time transport, zero cases, congruence and order compatibility
explicit. Force samples may distinguish rational representatives at finite
precision, so their errors must survive the estimates and vanish through the
proved completion. Removing those obligations would change the permitted
model, not merely shorten the proof.

There is also avoidable expansion. The harmonic route was built first, followed
by general sampled-force and calibrated versions. Compatibility retains the old
names, and both E and G are required, but separate proofs of the same finite
geometry and tolerance transport are unnecessary. The migration and shared
geometric-tail, finite-growth, FiniteSequenceGap and SampledValues estimates
already improve this. Some thin public compatibility facts still count once
per interface. For example, secantValue_realize and forceValue_realize are
definitional interfaces, not independent limit constructions.

The harmonic whole-edge module is the next concrete duplication risk.
HarmonicPolygonCurve's same-cell, adjacent-cell and zero-window alias arguments
need an actual shared-position join, not the harmonic force law. Its whole-edge
bound composes an affine vertex bound with an existing prefix-to-curve tail.
GeneralForceTime already supplies the general tail. Copying the harmonic file
would reproduce the alias machinery; one finite-vertex polygon core can support
both clients while preserving their existing public names.

## Limits of the reported substantive number

The classifier reads statements, not proof depth, use or mathematical novelty.
Its test 'sample' in the theorem name marks sampledName_equiv,
sampledValue_within, sampled_finite_area_law and sampled_polygon_velocity_bound
as numeric samples, despite their quantified general statements. Conversely,
it calls several rfl realization/embedding identities substantive because they
mention completed objects. Namespace/definition resolution and file ordering
can also change duplicate classification without changing a theorem statement.
Thus 995 is a reproducible category count, not 995 separate research advances.
The net rise of 494 in that category does not certify an equivalent rise in
discharged obligations. The README labels it as a heuristic, and the editorial
completion estimate remains tied to named bridges and their explicit premises.

## Next implementation rule

Use one Barrow finite-vertex polygon interface with proved position joining,
one binary-address alias proof, and the affine vertex estimate. Keep the
harmonic public declarations as compatibility clients, then construct the
general whole-edge polygon map and its uniform bound. Preserve both E and G,
all edition-local names and explicit force/sample premises. Measure the result
by reuse and the new general construction, even if preserving the public API
means the raw declaration count rises.

Then share matched-region/cover geometry where both clients really use it.
Retain cell closures, simultaneous connectors, overlap counted once and the
explicit final connector. A scalar enclosure alone would lose the constructed
region. Keep confinement, motion precision/partition independence, unrestricted
differentiation and potential estimates as separate obligations.

Avoid a broad rewrite or a theorem-count reduction campaign. New helpers should
support a live construction, combine genuine repeated estimates, or expose an
explicit source/proof boundary. Compatibility names and retained controls get
no independent completion credit. Any future classifier repair needs disclosed
before/after category changes and checks separating universal sampled laws from
closed numeric controls; a relabeling must not change the completion scores.

## Independent architectural review

At the user's explicit request, one sequential GPT-6 Astra reviewer read the
instructions, snapshot audit, both counting scripts and six representative
modules at 3f6d359. It did not rebuild or independently certify the mathematics.
Its assessment was "improving foundation, accumulating interface overhead."
The review identifies FiniteAccumulation.cross_actual_error_le_budget and its
same-map compatibility clients as genuine consolidation, and SampledValues's
diagonal Cauchy/name-equivalence construction as reusable completed-map work.
It also confirms the sample-name bias and the substantive classification of
the rfl gammaValue_address interface.

Astra recommends the next finite-vertex polygon extraction and general
whole-edge instance before a preliminary global-bound project. The actual
sample/coarse/shadow Conditions must stay explicit. Its following unit is the
general matched region with shared enclosure geometry and preserved final
connector; deriving more force-bound premises comes afterward. Counting and
reporting repairs should separate interfaces and controls from milestones.
Neither the review nor this note recommends discarding the retained APIs,
merging historical stages or importing a modern analytic primitive.

The raw counts and bounded review add no completion credit. All 16 sequential
handoff checks pass, including all three build targets, axiom/reference and
evidence/rendering tests. The catalogue remains at 1,371 distinct rows and
1,231 references, with the same standard axiom union and no Lean-library
source change. Logs: /tmp/newton-sol61-proliferation-final-01.log through -16.log.
Root Sol 6.1 commits this study and continues with the shared polygon core.

The follow-up now implements PolygonValues and GeneralForcePolygonCurve.
The harmonic alias, zero-window, affine-vertex and initial-endpoint proofs use
the same core, preserving their statements; the general map has uniform
whole-edge bound (T*V+A)/2^m. HarmonicGeneralPolygon identifies its harmonic
instance exactly with the retained map. This is a concrete second client,
without copying the harmonic polygon's alias proof suite. The next extraction
also now implements MatchedRegion with actual harmonic and general clients.
Cell closure, simultaneous connectors and covers share one proof suite; the
old harmonic statements and region remain intact. GeneralForcePathRegion/Content
construct the actual general all-cover cut and scalar with geometric decay.
The harmonic instance has exactly the retained region and scalar despite a
different cover bound. More public interfaces are added, while repeated proof
implementation is consolidated; raw growth is not itself a duplication finding.
