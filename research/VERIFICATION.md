# Verification record

## Current handoff: D.1, 4 October 2026

The foundation inventory changes documentation only. A sequential nonauthor
GPT-6 Luna worker reran the full README checks: both Lean 4.19 targets, formal
catalogue, source collation, graph/reference and axiom checks, edition
comparison, graph rendering, evidence regressions, source hashes, progress
regeneration and whitespace validation. All passed: 793 library theorems,
658 reference checks, 77 nodes/68 edges/247 passages, and only `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`. Progress at the checked parent
has 501 substantive declarations. Logs: `/tmp/newton-sol61-D1-01.log` through
`/tmp/newton-sol61-D1-14.log`. The foundation boundary has not yet migrated.
Completion scores are unchanged; the earlier dated entries below are historical
verification records, not counts for the current checkout.

## 22 September 2026 baseline and follow-ups

- Lean: 4.19.0, declared by lean-toolchain; default target is the library.
- `lake build` and `lake build NewtonLimitDynamics`: passed. The expanded
  library actually compiled; this is not the previous empty-default-build error.
- `catalogue_formal.py`: 97 theorem declarations inventoried, including private
  helpers, with actual signatures, source correspondence and premise boundaries.
- `check_graph.py`: 77 nodes, 68 classified edges, 234 passage records; source
  identity, TEI anchor/extract agreement and proof/proposed DAG acyclicity passed.
- `lake env lean research/CheckReferences.lean`: 94 public/reference declarations
  elaborated, with axiom inspection. Only standard Lean logical axioms
  `propext`, `Classical.choice`, `Quot.sound` occur; no project axiom or sorryAx.
- `test_evidence_validation.py`: valid baseline passed; stale edge URL,
  cross-stage proof edge, proof cycle and missing anchor were rejected.
- `compare_editions.py`: seven explicit passage alignments generated the report.
  Recorded incoming-edge changes are scoped to those proof passages.
- `collate_sources.py`: nine witnesses and 231 selected XML anchors collated;
  all generated extracts matched the TEI anchors, 51 anchors retained revision
  markup, and page/facsimile metadata was recorded. Local HTML anchor presence
  is reported separately (226 normalized and 231 diplomatic matches); three PDF
  or secondary records remain supplementary and unanchored. No image was
  downloaded or read.
- `sha256sum -c docs/SHA256SUMS`: all twenty-two listed source artifacts passed.
- `git diff --check`: passed. The manifest's external package list stays empty.

PDF verification was selective: Royal Society reprint p.36 (H4), Gregory p.336
(booklet proposal), p.339 (C44 identity). TEI checking is transcription checking,
not manuscript-image verification. C42 and exact Newton draft folios remain gaps.

These checks certify the stated Lean implications and data consistency. They do
not turn contact limits, mechanical area identification, curve existence or
secondary-supported manuscript mappings into discharged historical proofs.

Finite refinement-strip follow-up: Terra reran both builds, the formal
catalogue, graph/reference generation, Lean reference/axiom inspection and
whitespace check successfully. The new results use finite determinant and
triangle arithmetic only, with no integral calculus or limiting theorem.
They establish a spatially compatible one-cell strip, not a common-force time
refinement or an existing limiting curve. Source collation, archive hashes and
evidence regression results above are retained from the preceding validation;
unchanged sources were not revalidated for this code-only follow-up.

Time-subdivision follow-up: `lake build`, `lake build NewtonLimitDynamics`,
`catalogue_formal.py` (114 theorem declarations), `check_graph.py` (77 nodes,
68 edges, 234 passages, 106 Lean references), `CheckReferences.lean` (106
declarations inspected), and `git diff --check` passed. The new finite rational
diagnostic has no `sorryAx` or project axioms; only standard logical axioms
(`propext`, `Classical.choice`, `Quot.sound`) occur in dependency reports.
Its endpoint mismatch, equal terminal velocity, connector, and signed boundary
example are finite constructions only; no limiting curve, integral calculus,
or trajectory-existence claim is discharged.

Partition-control follow-up: `lake build` and `lake build NewtonLimitDynamics`
passed, and the regenerated catalogue contains 139 theorem declarations.
`check_graph.py` passed with 77 nodes, 68 classified edges, 234 passage
records, and 118 Lean references. `CheckReferences.lean` elaborated all 118
checked declarations; its axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or project axiom. The
new public results are finite: `partitionMotion_formula` explicitly unfolds
the repeated `TimeSubdivision.endKick` recurrence,
`candidate_partitionMotion_residual` gives the exact rational-time residual
`(Q/(2D²))*a`, and `residual_mesh_bound` gives its nonnegative maximum-cell
coefficient bound. No convergence, limiting curve, integral calculus, or
trajectory-existence claim is discharged. `git diff --check` passed; generated
`research/formal-results.json` was regenerated and conversation-export changes
remain preserved.

Zero-force follow-up (2026-09-22): `lake build` and `lake build
NewtonLimitDynamics` passed. `catalogue_formal.py` inventoried 165 theorem
declarations, and `check_graph.py` validated 77 nodes, 68 classified edges,
234 passage records and emitted 133 Lean references. `CheckReferences.lean`
elaborated 133 checked declarations and printed their axiom dependencies;
only standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`)
occurred, with no `sorryAx` or project axiom. `git diff --check` passed.
The zero-force results are finite rational-time constructions: recurrence
agreement with `p + t*v`, unchanged velocity, exact restart, independence of
positive common denominators and finite partitions, rest, and the within-cell
drift wrapper. The wrapper's bounds are explicit hypotheses and are not used
by its algebraic conclusion. The slow/fast example has distinct initial
velocities and therefore diagnoses insufficient identifying data rather than
nonuniqueness for fixed initial data. No continuum curve, all-Euclidean-time
realization, historical dependency, or action-constant conclusion is claimed.


Inertial-control follow-up (2026-09-22): `lake build` and `lake build
NewtonLimitDynamics` passed under Lean 4.19.0. The regenerated formal catalogue
contains 171 theorem declarations; `check_graph.py` validated 77 nodes, 68
classified edges, 234 passages, and emitted 138 Lean references.
`CheckReferences.lean` elaborated all 138 declarations. The aggregate axiom set
is `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project
axiom occurs. `git diff --check` passed. The explicit positive rational radius
controls both coordinate drifts for any rational base time and links the bound
to the actual zero-force end-kick cell. The epsilon-delta estimate is about
rational increments of the constructed inertial map; it does not extend the
map to all Euclidean times or establish a continuum curve or a historical
proof dependency. The generated formal-result ledger and reference checks were
regenerated; unrelated conversation-export edits were preserved.

Inertial-defect follow-up (2026-09-22): implemented by Codex; catalogue entry
and verification completed by Claude Code. `lake build` and `lake build
NewtonLimitDynamics` passed under Lean 4.19.0. The regenerated formal catalogue
contains 184 theorem declarations; `check_graph.py` validated 77 nodes, 68
classified edges, 234 passages, and emitted 146 Lean references.
`CheckReferences.lean` elaborated all 146 declarations. The aggregate axiom set
is `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project
axiom occurs. `git diff --check` passed. The result is signed determinant
cancellation for finite closed walks of rational-time inertial samples and for
four actual zero-force schedules; it gives no unsigned enclosure bound, timing
identification, or continuum curve.

Partial-cell follow-up (2026-09-22, Claude Code): `lake build` and `lake build
NewtonLimitDynamics` passed under Lean 4.19.0. The regenerated formal catalogue
contains 198 theorem declarations; `check_graph.py` validated 77 nodes, 68
classified edges, 234 passages, and emitted 158 Lean references.
`CheckReferences.lean` elaborated all 158 declarations. The aggregate axiom set
is `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project
axiom occurs. `git diff --check` passed. `candidate_partial_residual` gives the
exact residual `((Q+u*u)/(2D²))*a` at `(T+u)/D` against the actual partial
drift position, derived through the appended schedule `weights ++ [u]`;
`partial_squares_bound` and `partial_residual_mesh_bound` give the within-cell
mesh bound for `u≤w≤M`. These are finite rational-time position estimates;
no convergence, Euclidean-time realization, or central-force theorem is claimed.

Review and action-diagnostic follow-up (2026-09-22, Claude Code): `lake build`
and `lake build NewtonLimitDynamics` passed under Lean 4.19.0. The regenerated
formal catalogue contains 201 theorem declarations; `check_graph.py` validated
77 nodes, 68 classified edges, 234 passages, and emitted 161 Lean references.
`CheckReferences.lean` elaborated all 161 declarations. The aggregate axiom set
is `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project
axiom occurs. The auxiliary scripts `catalogue_m1.py`, `collate_sources.py`
(9 witnesses, 231 XML anchors), `compare_editions.py` (7 alignments),
`test_evidence_validation.py` (baseline plus four negative cases) and
`sha256sum -c docs/SHA256SUMS` passed without modifying tracked files; a
Haiku subagent ran them. `Diagnostic/InverseCubeAreal.lean` checks over natural-number
magnitudes that the Cor. 1 proportion with an inverse-cube comparison is
equivalent to equal squared areal velocity for two circles. It belongs to the
action diagnostic layer and is no historical proof. The review found stale
next-step notes (CONTINUATION, TIME_SUBDIVISION, ZERO_FORCE), now corrected,
and no mathematical errors in the checked modules.

Uniform-refinement follow-up (2026-09-22, Claude Code): `lake build` and `lake
build NewtonLimitDynamics` passed under Lean 4.19.0. The regenerated formal
catalogue contains 207 theorem declarations; `check_graph.py` validated 77
nodes, 68 classified edges, 234 passages, and emitted 165 Lean references.
`CheckReferences.lean` elaborated all 165 declarations. The aggregate axiom set
is `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project
axiom occurs. `git diff --check` passed. `uniform_refinement_small` gives, for
each positive rational tolerance and rational time `N/E`, an explicit unit-cell
refinement reaching that time with constant-force residual coefficient at most
the tolerance. It proves no sequence limit and no comparison of arbitrary partitions.

Partition-comparison follow-up (2026-09-22, Claude Code): `lake build` and
`lake build NewtonLimitDynamics` passed under Lean 4.19.0 without warnings. The
regenerated formal catalogue contains 216 theorem declarations (including
private helpers); `check_graph.py` validated 77 nodes, 68 classified edges, 234
passages, and emitted 167 Lean references. `CheckReferences.lean` elaborated
all 167 declarations. The aggregate axiom set is `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or project axiom occurs.
`git diff --check` passed. `partition_comparison` equates the residual-corrected
actual positions of two arbitrary schedules reaching equivalent rational times.
No limit or Euclidean-time claim is made.

Partial-comparison follow-up (2026-09-22, Claude Code): both builds passed
without warnings; 217 catalogued theorem declarations; `check_graph.py`
validated 77 nodes, 68 edges, 234 passages and emitted 168 references, all
elaborated by `CheckReferences.lean` with only `propext`, `Classical.choice`
and `Quot.sound`, and no `sorryAx`. `git diff --check` passed.
`partial_comparison` extends the exact two-partition comparison to partial-cell
sample times via the appended schedules.

Velocity-comparison follow-up (2026-09-22, Claude Code): both builds passed
without warnings; 219 catalogued theorem declarations; 169 references
elaborated with only `propext`, `Classical.choice` and `Quot.sound`, no
`sorryAx`; graph validation (77 nodes, 68 edges, 234 passages) and
`git diff --check` passed. `velocity_comparison` proves exact velocity
agreement of two arbitrary schedules at equivalent rational times.

Order-3 closure and Proposition II finite step (2026-09-22, Claude Code): both
builds passed without warnings; 230 catalogued theorem declarations;
`check_graph.py` validated 77 nodes, 68 edges, 234 passages and emitted 180
references, all elaborated by `CheckReferences.lean` with only `propext`,
`Classical.choice` and `Quot.sound`, and no `sorryAx`. `git diff --check`
passed. `partition_gap` packages the two-partition comparison.
`Polygon/Converse.lean` proves the finite Case-1 equivalence and its
counterexamples; it treats no realized curve, limit or moving centre.

Proposition II Case-2 finite step (2026-09-22, Claude Code): both builds passed
without warnings; 232 catalogued theorem declarations; 182 references
elaborated with only `propext`, `Classical.choice` and `Quot.sound`, no
`sorryAx`; graph validation (77 nodes, 68 edges, 234 passages) and
`git diff --check` passed. `extend_relative` and
`moving_centre_equal_areas_central` transfer the finite converse step to a
uniformly moving centre.

Central-schedule follow-up (2026-09-22, Claude Code): both builds passed
without warnings; 256 catalogued theorem declarations; `check_graph.py`
validated 77 nodes, 68 edges, 234 passages and emitted 196 references, all
elaborated by `CheckReferences.lean` with only `propext`, `Classical.choice`
and `Quot.sound`, and no `sorryAx`. `git diff --check` passed.
`CentralSchedule.lean` proves the finite area law for any central field with
unequal rational cells, exact one-cell refinement identities for an arbitrary
field, a harmonic example, and the unequal-cell converse. It proves no
convergence, curve existence, or force identification; see PROP_I_REALIZATION.md.

Passage-store extension (2026-09-22, Claude Code): twelve local TEI anchors
were added to `selections.json` with identifying translations. They are the
Section I Scholium (1687 par40/42, 1713 par46/48), Prop. IX (1687 par84–85,
1713 par108–109), Prop. XLI Cor. 3 (1687 par305, 1713 par335) and Prop. XLV
Cor. 1 (1687 par325, 1713 par355). They are comparison and diagnostic
witnesses for the action arguments and add no proof edge. `catalogue_m1.py`,
`collate_sources.py` (9 witnesses, 243 XML anchors), `compare_editions.py`,
`check_graph.py` (77 nodes, 68 edges, 246 passages), `test_evidence_validation.py`
and `sha256sum -c docs/SHA256SUMS` passed. Nothing was downloaded.

Harmonic-stability follow-up (2026-09-22, Claude Code): both builds passed
without warnings; 260 catalogued theorem declarations; `check_graph.py`
validated 77 nodes, 68 edges, 246 passages and emitted 200 references, all
elaborated by `CheckReferences.lean` with only `propext`, `Classical.choice`
and `Quot.sound`, and no `sorryAx`. `git diff --check` passed.
`HarmonicStability.lean` proves the exact equal-cell invariant for the linear
central field and its completed-square form. The boundedness inequality chain
and any convergence are not formalized.

Harmonic-bound follow-up (2026-09-22, Claude Code): both builds and the
reference/axiom check passed (only `propext`, `Classical.choice`,
`Quot.sound`; no `sorryAx`). `schedule_speed_bound` and
`schedule_position_bound` formalize the mesh-uniform stability inequalities.

Action arguments for a nonzero constant (2026-09-22, Claude Code, at the
user's direction): both builds passed without warnings; 284 catalogued theorem
declarations; `check_graph.py` validated 77 nodes, 68 edges, 246 passages and
emitted 220 references, all elaborated by `CheckReferences.lean` with only
`propext`, `Classical.choice` and `Quot.sound`, and no `sorryAx`.
`git diff --check` passed. `Diagnostic/PhaseArea.lean` checks the rigid-shear
structure of the construction's cell for every field, exact phase-triangle
area for affine fields at every duration, and a duration-dependent
energy-type invariant. `Polygon/MonotoneEnclosure.lean` checks the finite
enclosure under the 1713 Lemma X clause and a non-monotone escape.
Arg004–Arg006 cite only passages already in the store. No passage store
change, download, or proof edge.

Proposition III finite-step follow-up (2026-09-28): both builds passed under a
locally rebuilt Lean 4.19.0. That toolchain was compiled in this environment
from the upstream `v4.19.0` source (`stage0` bootstrap, `-DUSE_GMP=OFF`, libuv
1.48.0 built locally) because the release-binary hosts are unreachable here;
`lean --version` reports `4.19.0-pre, Release` for the stage0 binary.
`catalogue_formal.py` inventoried 300 theorem declarations, and `check_graph.py`
validated 77 nodes, 68 edges, 246 passages and emitted 236 Lean references.
`lake env lean research/CheckReferences.lean` elaborated all 236 declarations;
the aggregate axiom set is `propext` (178), `Quot.sound` (149) and
`Classical.choice` (25), with no `sorryAx` and no project axiom. The other
Python checks, `sha256sum -c docs/SHA256SUMS` (22/22) and `git diff --check`
passed. `Polygon/RelativeMotion.lean` adds 16 declarations; the six
Proposition III dependency edges now carry formal references. The results are
finite two-body polygon identities: no limiting curve, no parallelogram
composition of simultaneous forces, and no force/mass/time-scale reading is
derived.

## Merge corrections verified on 1 October 2026

Reviewed merge `381d5e9`. `propIII_via_moving_centre` now accepts the original
relative-area hypothesis, adds the opposite reference deflection to both
histories using `corVI_relative`, identifies the reduced reference motion by
Law I at the correct vertex times, and applies the Proposition II moving-centre
converse. `moving_centre_alignment_example` checks the three-vertex timing
counterexample. These remain finite integer-coordinate reconstructions;
inward sense, force interpretation and trajectory realization are separate.

The false absolute-area completion claim was removed from the module comments,
state, queue and generated catalogue. `StripArea.lean` proves the signed sum
only; absolute polygon-strip sums and their geometric decomposition remain
open. The state and queue now name the existing `RelativeMotion.lean` results
instead of the absent module and declarations. Circle-comparison comments now
distinguish the supplied circle relation from proved algebra and record the
full-chord coefficient `1/(8r)` in the unproved limiting route.

The local Elan installation had no toolchain. The pinned upstream Lean 4.19.0
release was streamed into `/tmp/newtonlean-core-4.19.0`, extracting only the
Lean/Lake executables, runtime shared libraries and core/Std `.olean` files.
No archive, mathlib or external-package cache was installed. Its version is
`4.19.0`, release commit `6caaee842e94`. Both build targets and the reference
check passed:

```sh
/tmp/newtonlean-core-4.19.0/bin/lake build
/tmp/newtonlean-core-4.19.0/bin/lake build NewtonLimitDynamics
/tmp/newtonlean-core-4.19.0/bin/lake env lean research/CheckReferences.lean
```

The catalogue inventories 319 theorem declarations; the evidence checker
validates 77 nodes, 68 edges and 246 passages and emits 245 Lean references.
All 245 references elaborated. Axiom inspection reports only `propext` (215),
`Quot.sound` (155) and `Classical.choice` (28); no `sorryAx` or project axiom.

All seven SVGs parse as XML after fixing the malformed bold attribute.
`test_graph_rendering.py` checks generated SVGs and distinct solid, dashed,
dotted and dash-dot raster patterns, including the stage/status legend.
PNG previews and the seven-page grouped PDF were regenerated; representative
figures were visually inspected. The evidence-validation baseline and four
negative cases, all 22 source checksums, and `git diff --check` passed.

## Overnight first increment, 3 October 2026

Lean 4.19.0 `lake build` and `lake build NewtonLimitDynamics` passed. The
catalogue has 346 theorem declarations in 35 modules; the graph validates
77 nodes, 68 edges, 246 passages and emits 272 Lean references. A separate
verification agent elaborated every reference and axiom report with no errors,
sorryAx or project axioms; the aggregate set is propext, Classical.choice,
Quot.sound. Evidence validation, graph-rendering controls, all 22 source
checksums and whitespace checks passed. New graph coverage rendering is
deferred until the next proof batch; existing seven figures passed integrity
checks, and their earlier corrections are preserved.

The new finite support includes unsigned equal-cell/block sums, separately
named De Motu witnesses and 1687/1713 statements, and finite path-defect
accounting. A fresh `Std` direct-det calculation independently checked the
two-lobe example: signed/unsigned Kepler sums agree at -6/6 while the unsigned
patch budget is 2. A deliberately false statement was rejected by Lean.
The De Motu catalogue now uses declaration-specific witness references.

No actual trajectory is constructed by this increment. The stage defect-control
interfaces assume the nonnegative polygon–trajectory region's geometric
enclosure and a vanishing budget and are diagnostic variants only. The primary
forward construction remains open, with Proposition I prioritized over II–IV.

Harmonic common-time follow-up: both full builds passed. The catalogue now has
360 theorem declarations in 36 modules; all 286 references elaborate with only
propext, Classical.choice and Quot.sound, no sorryAx or project axiom. The
reference run started before root-library compilation had completed failed on
the new names; its correctly ordered rerun passed. The local construction
checks position/velocity mismatch, triangle reduction, exact cubic closed
defect, equal Kepler sums and the pinned -1/8 signed versus 1/8 absolute gap.
It supplies no actual trajectory or accumulated global defect estimate.

Absolute-arithmetic follow-up: both full builds and all 301 references passed
sequentially; 375 catalogued declarations in 36 modules. Axiom set remains
propext, Classical.choice, Quot.sound, with no sorryAx/project axiom. The new
Fraction magnitude respects unnormalised value equivalence and has product,
sign and triangle estimates; order transport handles equivalent values and
zero factors. The checked strict cancellation example guards unsigned sums.
The local harmonic unsigned gap is now identified with its exact cubic
magnitude. These are finite arithmetic estimates, not trajectory existence.

Finite perturbation follow-up: both full builds passed, followed in order by
the catalogue, graph validation and all 322 reference/axiom checks. There are
403 declarations in 38 modules. The axiom set remains propext, Classical.choice
and Quot.sound, with no sorryAx/project axiom; whitespace checks passed.
Point/state L1 triangle, scaling and equivalence estimates support the actual
harmonic cell's derived amplification and one-step perturbation estimates.
Zero-duration and w=1,h=1/2 controls compile; Lean rejects the false temporary
norm-cancellation assertion. These estimates do not yet compare whole schedules,
construct a trajectory or identify a geometric nonnegative intervening region.

Global accumulation follow-up: both full builds and all 342 reference/axiom
checks passed, with catalogue/graph validation and whitespace checks in order.
There are 445 declarations in 39 modules; only propext, Classical.choice and
Quot.sound are reported, with no sorryAx/project axiom. The module identifies
actual coarse/fine recurrences with their equal-time schedules and proves the
local truncation estimate, two-cell perturbation estimate, coarse-state power
bound and nonnegative global error recurrence. Exact zero/one/two-block controls
pass, including actual errors 13/16 and 173/256; Lean rejects the false one-block
endpoint equality. Mesh-uniformity, realization and geometric area remain open.

Finite growth follow-up: both full builds and all 360 reference/axiom checks
passed, with catalogue/graph and whitespace checks. There are 464 declarations
in 40 modules; the axiom set remains propext, Classical.choice and Quot.sound,
with no sorryAx/project axiom. The common-denominator cofactor estimate and
small-total uniform amplification bound are proved by finite integer induction.
Empty/zero increments, list identities and a boundary sample compile. Lean
rejects the deliberately false bound in `/tmp/NewtonFiniteGrowthFalse.lean`
when smallness is removed. Application to actual harmonic powers remains next;
no completion, geometric area or historical analytic theorem is supplied.

Uniform harmonic follow-up: both full builds and all 381 reference/axiom
checks passed in order, followed by whitespace checks. There are 514
declarations in 41 modules; only propext, Classical.choice and Quot.sound,
no sorryAx/project axiom. Actual coarse/fine factor powers and states obey
uniform bounds under h≥0 and T*(1+|w|)≤1/2; actual state error is at most
3*T*h*|w|*M. The displayed T is proved equivalent to both actual elapsed
times. Exact boundary error 145/4096, bound 3/16 and zero controls compile;
the false unrestricted factor-two claim is rejected. The time threshold
uses a coordinate/unit calibration. Trajectory and intervening-area geometry
remain open, so this is finite construction support, not full Proposition I.

Daytime unsigned-triangle follow-up, 4 October: both full builds and all 395
reference/axiom checks pass; 531 declarations in 42 modules, with catalogue,
graph and whitespace validation. The axiom set is still propext,
Classical.choice and Quot.sound, with no sorryAx/project axiom. Determinant
magnitude and incident/consecutive-edge triangle estimates hold for arbitrary
rational representatives. Unsigned magnitudes are nonnegative, translation
invariant and unchanged by reversed vertex order. Opposite signed patches
retain their magnitude sum. A false unsigned-equals-signed claim is rejected
in `/tmp/NewtonTriangleMagnitudeFalse.lean`. Patch multiplicity is explicit;
geometric region coverage and limiting trajectory remain separate obligations.

Finite geometric-cover follow-up, 4 October: both full builds pass, followed
in order by catalogue/graph validation and all 428 reference/axiom checks.
There are 590 declarations in 44 modules. Only propext, Classical.choice and
Quot.sound appear; no sorryAx/project axiom or compiler warning/error.
Convex interpolation and actual prefix estimates derive the two matched
half-cell enclosures, with nonnegative square-cover budget
2*T*h*M²*(4+3*T*|w|)². Exact boundary and zero controls pass. The eighth-radius
coordinate-square claim is deliberately rejected in
`/tmp/NewtonHarmonicSquareFalse.lean`; the separate quarter-radius L1-ball
failure is not a square failure. Reference log:
`/tmp/newtonlean-day-cover-refs.log`. Whitespace checks pass. Point containment
and the square-area sum do not assert union content, a realized trajectory or
its actual intervening area. The next check uses the frozen-snapshot arithmetic
holdout protocol in [verification provenance](VERIFICATION_PROVENANCE.md).

The sequential nonauthor check of frozen `15d50ad` reproduced both builds,
catalogue/graph and all 428 references. Counts refer to 44 declaration-bearing
modules (45 Lean files): 427 public catalogue theorems plus the public
QuadraticInitialDeflection proposition explain the 428 reference targets.
The third fresh signed two-block arithmetic holdout passed; its altered-radius
comparator was rejected as a false equality. The earlier two invalid harness
records are excluded. Exact standalone/comparison sources, hashes and logs
are retained in [the holdout artifact](verification/harmonic-cover-2026-10-04/README.md).
Its scope is implementation arithmetic for one case, not generic geometry or
existence; no project repair was made from the reference.

Actual dyadic Cauchy-data follow-up, 4 October: both full builds, catalogue,
graph and all 453 reference/axiom checks passed in order; 631 declarations in
45 declaration-bearing modules. Only propext, Classical.choice and Quot.sound,
with no sorryAx/project axiom, warning or error. `endpointName` was separately
type/axiom checked as well as its public Cauchy theorem. The sequence is
identified with actual schedules of elapsed time T, arbitrary finite gaps
and two later endpoints obey the geometric tail bounds, and finite integer
arithmetic derives the explicit positive-tolerance modulus. Zero time is
generic; the production-side exact adjacent/cap controls pass. Lean rejects
the false zero-error claim in `/tmp/NewtonHarmonicDyadicFalse.lean` as false.
Reference log: `/tmp/newtonlean-day-dyadic-refs.log`. Whitespace checks pass.
This constructs fixed-rational-time Cauchy names; it supplies neither a limit
point nor continuous time-domain realization, partition independence or the
actual polygon–trajectory area. The earlier holdout certifies only its frozen
cover snapshot and is not reused to certify this construction.

Uniform rational-time follow-up, 4 October: both full builds, catalogue,
graph and all 485 reference/axiom checks pass in order; 665 declarations in
46 declaration-bearing modules. Only propext, Classical.choice and Quot.sound
appear, with no sorryAx/project axiom, warning or error. `timeName` and
`timeDelta` were separately type/axiom checked. The actual schedules satisfy
the pinned level-independent coefficient4 bound, and eps/(L+1) constructs a
positive tolerance even when M=0. Generic same-time and zero-state controls
and exact production values19/64,24,3 compile. The deliberately false
zero-error control in `/tmp/NewtonHarmonicTimeFalse.lean` is rejected as false.
Reference log: `/tmp/newtonlean-day-time-refs.log`. Whitespace checks pass.
This verifies a rational-time map of derived Cauchy names; realization in a
completed point space, identification with one global polygon family, force
identification and the actual intervening area remain open. The earlier
frozen-snapshot cover holdout is not reused as an oracle for this increment.

Actual binary-prefix Cauchy-data follow-up, 4 October: both full builds,
catalogue, graph and all 523 reference/axiom checks pass in order; 702 library
declarations in 47 declaration-bearing modules. Only propext, Classical.choice
and Quot.sound; no sorryAx/project axiom, warning or error. The `prefixName`
and sample data constructors were separately checked. Every binary address
selects actual prefixes of one global family; tick bounds, actual elapsed-time
control, state bounds, adjacent and finite geometric tails, and the explicit
positive-tolerance modulus compile. Generic all-zero/zero-time controls and
production values17/64,19/8,545/65536 pass. The false first zero-error statement
is rejected specifically as false in `/tmp/newtonlean-prefix-false.lean`.
Reference log: `/tmp/newtonlean-day-binary-refs.log`. Whitespace checks pass.
The separately retained long-time scope control also compiles, proving the
time coefficient fails without smallness, with propext only. No completed
point/time realization, address independence, force law or actual D_mesh is
claimed. Earlier arithmetic holdouts remain limited to their fixed snapshots.

Cauchy-value realization follow-up, 4 October: both full builds, catalogue,
graph and all 547 reference/axiom checks pass in order; 744 declarations in
48 declaration-bearing library modules. The only axioms are propext,
Classical.choice and Quot.sound, no sorryAx/project axiom or warnings/errors.
The value and bound constructors were separately type/axiom inspected.
Name equivalence and constant-state separation are proved; bound invariance
precedes quotient lifting. Symmetry, triangle and zero-radius iff equality,
constant-approximant convergence, rational-time control and actual prefix-tail
value bounds compile. The all-level3/16 sample lower bound and positive
non-equality theorem prove state-value separation. The false equality test
fails by rfl; this supplementary failure is not the mathematical evidence for
non-equality. Reference log: `/tmp/newtonlean-day-values-refs.log`. Whitespace
checks pass. This constructs values in the explicit name quotient, not an
assumed external complete coordinate space, quotient time domain, position-only
motion or actual intervening area.

The sequential nonauthor Luna check reproduced the two builds and all547
references on frozen `92b8a9f23c1add8cfcd0606022b83ebcd3e5ddfc`. Catalogue/graph
regeneration in a temporary snapshot matched the checkout at744 declarations,
48 modules and77 nodes/68 edges/246 passages. Constructor/premise inspection
confirmed bound invariance before lifting, zero-radius separation and the
positive sample non-equality proof, with only the same standard axioms. The
retained short-time scope artifact and whitespace check passed. No numerical
holdout or oracle was used. Log: `/tmp/newtonlean-92b8a9f-references.log`.
The unrelated conversation-export changes were preserved; no repair was made.

Binary-time motion follow-up, 4 October: both full builds, catalogue, graph
and all 612 reference/axiom checks pass; 806 declarations in 50 declaration-bearing
modules. Only propext, Classical.choice and Quot.sound; no sorryAx/project
axiom, warning or error. Time-name/setoid/domain and motion/time-coordinate/
tolerance constructors were separately type/axiom inspected. Same-grid state
control, address independence before the quotient lift, closed-radius and
uniform continuity, state endpoints, injective time coordinates with endpoints
0/T, aliases and zero cases compile. Exact alias controls and sample left/right
state separation pass. The finite-prefix alias equality is rejected specifically
as false in `/tmp/newtonlean_false_time_state.lean`. Reference log:
`/tmp/newtonlean-day-binary-time-refs.log`. Whitespace passes. The result is a
continuous state map on its explicitly constructed binary-time quotient;
position geometry, actual region/content, partition independence and force
identification remain separate. No old holdout is reused for this construction.

Planar-position follow-up, 4 October: both full builds, catalogue, graph and
all 645 reference/axiom checks pass; 843 declarations in 51 declaration-bearing
modules. Only propext, Classical.choice and Quot.sound, no sorryAx/project
axiom, warning or error. Generic name/value map, planar fixed-point type,
gammaPosition, nonnegative radius and completed-square constructors were
separately type/axiom inspected. Equivalence preservation precedes quotient
lifting; idempotence and closed-bound preservation are proved. Continuity,
alias/endpoint identities and zero cases compile. Eventual coordinate bounds
imply completed-square membership; the radius-1 corner has L1 distance 2.
The sample's level-1 position distance 135/512 and tail 3/16 give lower 39/512
at every later level and positive projected endpoint/right-left separation.
Lean rejects finite position equality specifically as false in
`/tmp/newtonlean_position_false.lean`. Log:
`/tmp/newtonlean-day-position-refs.log`. Whitespace passes. No actual polygon
map, connector region, area content, partition independence or force law is
claimed, and no previous holdout is reused as an oracle.

The sequential nonauthor Luna review of frozen
`a42f5474eb22ba80ee46b0718931c82dd353ea65` reproduced both builds, all 645
reference/axiom checks, constructor checks and unchanged generated artifacts
from a temporary snapshot at 843 declarations in 51 modules. Time-coordinate
injection and endpoint times, equivalence before lifting, planar fixed-point
semantics and coordinate-square predicates retain their intended premises.
The positive position separation is supported by the all-level lower bound.
No scope defect, numeric holdout or repair; only the same standard axioms.
Log: `/tmp/newtonlean-a42f547-references.log`, SHA-256
`bdb3812d58bc754f058c87357af1c4983044a8834b238716636fa5dd9d3d6543`.

Duplicate-helper consolidation, 4 October (Claude Code): 50 duplicated helper
theorems are merged into one canonical copy each, taking the library from 843
to 793 theorems. Fraction congruence, distributivity and sign lemmas
(`add_equiv`, `mul_equiv`, `add_equiv_left`, `mul_equiv_right`,
`le_add_nonnegative`, `nonnegative_add`, `nonnegative_mul`, `add_zero`,
`mul_zero`, `add_mul`) now live in `Common/RationalMagnitudes.lean`; point
equivalence lemmas and `det_add_right` in `TimeSubdivision`; `point_le_state`
and `velocity_le_state` in `PointBounds`; `HarmonicUniform.two_mul` is public.
Each canonical statement equals the removed copies up to variable names, and
each kept proof is one of those copies. The removed public names
`HarmonicDyadic.add_equiv`, `HarmonicDyadic.mul_equiv`,
`HarmonicTimeComparison.add_num_nonnegative`,
`HarmonicTimeRealization.mul_add_equiv` and `CentralSchedule.det_add_right`
have their call sites moved to the canonical lemmas. Stage-local restatements,
the per-edition Lemma X pair, the two Proposition III routes and same-named
lemmas about distinct definitions (HarmonicBinaryPrefix tails, samples) are
retained deliberately. Both builds pass with no warning; the catalogue has 793
theorems; all 658 reference/axiom checks pass with only propext,
Classical.choice and Quot.sound and no sorryAx; evidence validation and
whitespace pass. Mathematical content, premises and source classifications
are unchanged.
