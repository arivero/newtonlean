# Verification checklist

Use Lean 4.34.1 core/Std only, with no mathlib, sorry or project axioms.
Choose the mathematical increment using [PROOF_STRATEGY.md](PROOF_STRATEGY.md).
This checklist verifies that increment; passing it alone does not establish
that the selected theorem advances the historical target.
Run from the repository root:

```sh
lake build
lake build BarrowLib
lake build ClassicsLib
lake build ModernLib
lake build NewtonLimitDynamics
lake build Reverse
lake env lean research/CheckReferences.lean
lake env lean scripts/inspect_graphs.lean
sha256sum -c docs/SHA256SUMS
git diff HEAD --check
```

The default build alone is insufficient. `CheckReferences.lean` inspects
compiled project constants: it permits only propext, Classical.choice and
Quot.sound in safe declarations, propagates anachronical use through types,
bodies and private helpers, classifies historical sections by source position
relative to the five-line `ANACHRONICAL PROOFS` header, and verifies the
opening `Modern dependency score` comments against compiled transitive
dependencies. Passing does not discharge geometric or mechanical premises.
Compiler-generated auxiliaries, including the equation lemmas that `simp`,
`rw` and `unfold` realize on demand, are classified at their parent
declaration's source position; they depend only on that declaration.

After changing a proof, build, refresh the score comments, rebuild (inserted
comments shift source positions) and check:

```sh
lake build
lake build BarrowLib
lake build ClassicsLib
lake build ModernLib
lake build NewtonLimitDynamics
NEWTON_WRITE_PROOF_SCORES=1 lake env lean research/CheckReferences.lean
lake build
lake build BarrowLib
lake build ClassicsLib
lake build ModernLib
lake build NewtonLimitDynamics
lake build Reverse
lake env lean research/CheckReferences.lean
```

The refresh edits proof comments in place. Types and private helpers are
traversed; Lean infrastructure, generated auxiliaries and the proof itself are
excluded. A score describes repository classification; it cannot establish
the original attribution of a result.

## Encoding migrations

For the authorized 4.34.1/Rat migration, compare the scratch baseline of all
project theorem names/types and historical `#print axioms` reports before
changing representation. The toolchain-only stage must retain statements and
named theorem counts; later Rat stages must preserve mathematical meanings
and historical names. Distinguish printing changes from statement changes.
Keep baseline outputs in scratch, and report representative-sensitive stop
conditions. Core arithmetic is outside project M/H scores; exact historical
attestations remain a separate source obligation. No migration or relocation
earns completion credit. Time the same six warm builds before and after.
The temporary bridge must prove the Rat roundtrip, equiv/order/positive
correspondences and operation laws, with durationDifference sigma tau mapping
to tau - sigma. Relocated negation/time-difference definitions retain their
bodies and fully qualified names; existing historical statements and axiom
sets must remain unchanged at this additive stage.

Replace deprecated names with the names in Lean's messages using the patch
tool. Require zero deprecation warnings across all six builds. Compare the
cleanup's theorem names/types and counts with its immediate predecessor and
the frozen Stage 0 baseline, identifying previously authorized Rat changes
separately. Do not suppress warnings. Remove unused simp arguments as each
module migrates, requiring no warnings in migrated modules; restore any
argument whose removal breaks a proof and report its location. After Stage 3,
sweep the remaining files in one commit and report warning counts by kind.
The deprecation-only increment leaves the current README theorem/dependency
counts unchanged. Its six-build warning census changes deprecations from
70 to zero, while retaining 543 unused-simp and five proposition-as-definition
warnings for their authorized migration/sweep stages. The initial 4.34.1
census was 545 unused-simp warnings in 107 files; RationalExhaustion's Rat
rewrite removed two before the deprecation cleanup.
FiniteGrowth's migration removes one more unused-simp warning. Its uniform
bound and numeric counterexample remain checked, with the controls stated as
anonymous examples. No removed simp argument has needed restoration so far.
RationalTolerance retains one shared weak bound over Rat; positivity and
strict control close inline. Verify equality of the old and new tolerance
values in scratch as well as the theorem/axiom dumps and all six builds.
RatUltimateScaling is proved directly over Rat. Retain the legacy higher-order
API until its callers can change domains together; normalized sampling is not
a reverse bridge for arbitrary representative-sensitive Fraction functions.
Scratch checks distinguish equivalent representatives and verify that the
example vanishes on every normalized representative. They do not by themselves
formalize a full limit countertheorem. No equivariance premise may be silently
added to a historical statement.
FiniteSequenceGap's carrier parameter removes unused coordinate imports; its
four callers convert only scalar distance values. Verify their public types
and all historical axiom reports unchanged, together with the existing
harmonic-time scope harness. Actual state representatives must not change as
a side effect of migrating this estimate.
RationalIntervals removes six redundant helpers and defines the midpoint over
Rat. Legacy state inputs keep their original midpoint expressions until those
domains migrate. The monotone-rectangle and magnitude-content harnesses pass,
and historical theorem types and axiom reports are unchanged. The finite-gap
rewrite removed two unused-simp warnings; interval bisection removes seven
more. The current six-build census is 533 unused-simp, zero deprecation and
five proposition-as-definition warnings. No simp argument has been restored.
The subsequent active scalar-power cutover removes two more unused-simp
warnings, leaving 531. FiniteAccumulation and FiniteRecurrence retain legacy
sections and are not yet fully migrated modules. Check that factorPower is
core Rat, that only scalar bounds cross the bridge, and that both final
uniform-error statements and all historical theorem types/axiom reports are
unchanged. The regional-accumulation harness passes. Two named helpers are
deleted (one core duplicate, one redundant transport wrapper); the shared
lower-bound induction and necessary temporary fpower correspondence remain.
FiniteRecurrence is subsequently fully migrated to Rat: require zero warnings
in it and Common/FinitePowers. Six old helpers are removed; the shared power
induction and fpower correspondence move, and one temporary legacy bound
adapter is added. Check the old/new recurrence values by a scratch induction
for arbitrary signed coefficients. Every ofRat output at these call sites
must remain a numerical bound, never a state/callback/duration/count input.
All six builds and the regional accumulation, regional construction and
given-trajectory controls pass. Historical theorem types/axiom reports and
final uniform-error types remain unchanged. The warning census is now 524
unused-simp, zero deprecation and five proposition-as-definition warnings.
No removed simp argument required restoration.
For provenance rows, require S + R + P + U to equal the same compiled proof
tree shown in the measurements; wrapped scratch output must not skip rows.

## Review the conclusion before accepting progress

Read the changed theorem's full statement alongside the previous result and
the exact historical passage. Identify the obligation it now proves and every
premise it still supplies. A new hypothesis containing the missing conclusion
does not discharge that obligation. A deliberately conditional theorem must
be reported with its conditions, including whether their joint realization
has been established in the intended domain.

Check that the historical client actually uses the new mathematical result
through the compiled dependency graph. Distinguish a new conclusion, a removed
premise and an enlarged domain from an edition wrapper or structural cleanup.
Counts describe all of those changes; completion estimates must reflect the
remaining mathematical work. Compare proof sizes only at the same scope:
one theorem versus one theorem, or a complete shared development versus another.
Neither a short proof body nor a smaller import graph establishes sufficiency.

## README measurements

The existing checker also reports source lines, source-declared theorems and
distinct theorem counts in compiled proof and import graphs, including each
ClassicsLib source file as well as the historical files. After rebuilding:

```sh
NEWTON_PRINT_THEOREM_COUNTS=1 lake env lean research/CheckReferences.lean
NEWTON_CHECK_README_COUNTS=1 lake env lean research/CheckReferences.lean
```

The print mode supplies Markdown rows for the README; the check mode rejects
missing, stale or duplicated measurement rows. Neither mode writes files.
Added 8 October 2026: the default axiom, taint and score checks retain their
previous behavior; these optional reports reuse their compiled graph.

Lines include comments, Latin and blanks. Named source theorems, including
private theorems, count once; definitions, anonymous examples, generated
auxiliaries and Lean/Std declarations are excluded from the theorem counts.
Proof trees include the file's own theorems and all project theorems reached
from its declarations, traversing types, definitions and private helpers.
Import trees include its own theorems and all project theorems available
through its compiled imports. Both primary and anachronical sections count.
The three library rows aggregate their own modules and entry point, with
dependencies counted once across the whole library.

Synthetic known-answer controls cover duplicate/shared dependencies, an
unreachable theorem, scope exclusion, definition traversal, empty inputs,
line endings, and rejection of a corrupted or duplicated README row. Live
controls check that both printed Lemma I before-end theorems are classified
in their owning source file. Compare direct counts and line totals with the
source; the proof/import distinction requires compiled dependencies. These
measurements describe existing work. The completion percentages separately
estimate work done / (work done + estimated remaining work).

`inspect_graphs.lean` regenerates `research/figures.md`, distinguishing
witness-specific source evidence, editorial comparisons, library imports and
direct formal uses. A missing source-comment edge does not establish
historical absence. Compare historical Latin with its named archived TEI,
including additions/deletions, omitted forme-work, source hashes and
witness-specific wording.

## Proof scope controls

`uniform-rectangles-2026-10-10.lean` checks the nonmonotone area-exhaustion
extension of both editions' Lemmas II/III and Corollary I. The graph
`|t-1/2|` is proved uniformly continuous and nonnegative, and is proved not
increasing on the unit interval. Actual dyadic partitions realize arbitrarily
small mesh; a returned delta gives a usable tail with both assigned-area
errors. Finite controls exercise the clipped lower height at zero and above
the tolerance, and refute the old endpoint lower enclosure on this graph.
Compiled traversal requires the edition's own new clients, actual finite
rectangle areas, the sum gap bound, X.1 halving and the finite magnitude-error
comparison. Foreign witnesses and ModernLib are rejected. No Lemma I use is
asserted for this alternative construction. The area convention and arbitrary
curved-area magnitude remain supplied; there is no nonrational model, new
ratio theorem or general boundary-convergence conclusion.

`magnitude-content-2026-10-09.lean` checks the enlarged assigned-area domain
of both editions' Lemmas II/III and Corollary I. Actual dyadic identity-graph
partitions realize the geometric/mesh premises for arbitrary supplied `A : Q`,
without an image-of-rationals assumption. The legacy adapter preserves the
partial area relation, accepts unreduced rational displays, and proves
zero-height approximation from the rectangle rule alone. A fixed-gap
enclosure is rejected as nonconvergent; a lexicographic infinitesimal control
rejects unit-halving exhaustion without the classical condition. The latter
is a comparison counterexample, not a model of every area rule.
Compiled traversal requires the edition's own enclosure, exhaustion and
Lemma I, the reused finite area proof and `Rules.unit_halves_exhaust`; foreign
witnesses and ModernLib owners are rejected. Only the rational magnitude
model is realized. The arbitrary magnitude domain and geometric area
convention remain supplied, with no constructed nonrational area model or
general magnitude-ratio theorem. A bounded sequential Sol review found no
blocking issue in the pullback and comparison proof. These checks share the
kernel and rational arithmetic and do not establish general area existence.
The Greek X.1 and V.4–5 archive companions record the selected reading and
the exact classical-premise/source boundary.

The same harness also checks the integer-multiple unit-ratio extension of
both editions' Lemmas II/III. Its dyadic identity patch has zero first lower
sum and a positive interior rectangle; all four general assigned-magnitude
clients compile and a returned tail yields an actual 2:3 comparison.
Equal positive constants pass. Zero/zero, constant ratio 1:2 and shrinking
areas with ratio 1:2 are rejected; the last case has a proved vanishing gap.
Compiled traversal requires the shared bracket derivation, multiple-order
proofs and explicit compatibility laws, rejecting foreign witnesses and
ModernLib. The supplied order laws have a rational realization and contain
no ratio convergence premise. A bounded sequential Sol review found no
invalid implication. The result concerns eventual comparisons for each fixed
unequal positive integer pair, not exact finite Euclid V.5 equality, a full
ratio calculus, a separate abstract `positive A` conclusion or area existence.

```sh
for check in research/verification/*.lean; do
  lake env lean "$check" || exit 1
done
lake env lean research/verification/harmonic-cover-2026-10-04/reference.lean
lake env lean research/verification/harmonic-cover-2026-10-04/comparator.lean
```

The deliberate corruption must fail:

```sh
lake env lean research/verification/harmonic-cover-2026-10-04/corrupted-comparator.lean
```

The expected rejection is `decide` refuting the radius equality whose
numerator was increased by one; treat an import error or timeout as a broken
control. The reference/comparator share the model and Lean kernel, so they
check the proposed formula's implementation rather than independent geometry.

Each harness's opening docstring states what it controls. An `AreaRules` or
`DifferenceAreaRules` argument is an explicit geometric premise; a control
with that argument does not prove that such a convention exists. Complete
hypotheses live in the owning declarations. Results, the latest verification
record and open obligations live in [STATE.md](STATE.md).

`lemma3-staircase-boundaries-2026-10-09.lean` distinguishes explicit step
edges from filled endpoint boxes. It rejects both an interior box point and
the false final rise above the last lower rectangle, includes internal joins
in adjacent/repeated cells, and transports equivalent rational coordinates.
Flat graphs and a collapsed interval are allowed. A nonzero identity graph
with actual dyadic partitions realizes continuity and mesh exhaustion; the
reverse approach estimate reaches the omitted final graph endpoint on a
usable tail. Compiled traversal requires each edition's own rectangle-cover
theorem, the node/sandwich proofs, all four node/box inclusions and both actual
rectangle-union inclusions. It excludes foreign witnesses and ModernLib by
compiled module ownership. The new argument uses no area assignment and
claims no fixed-side, full topological perimeter or arclength conclusion.

`classical-comparisons-2026-10-08.lean` checks the two arithmetic comparisons:
empty/repeated collections and a composite common-multiple-plus-one for
Euclid, and unreduced/signed ratios and the necessary denominator restriction
for √2. Compiled traversal requires the prime-divisor/product and parity/halving
helpers and excludes BarrowLib, ModernLib, Newton and mathlib. These checks
share Lean core arithmetic and the kernel; the source-level mathlib review
does not claim to enumerate that library's compiled transitive dependencies.

`lemma2-3-monotone-rectangles-2026-10-06.lean` checks the positive-base and
interior-positive mutual-ratio increments. For `g(x)=1+x²`, exact aliased-node areas `9/8` and
`13/8` give ratios `9/13` and `13/9`; the perturbed ratio `10/13` is rejected.
Repeated nodes, unequal cells, constant graphs and zero-area degeneracies
exercise the finite base bound. All four printed-edition clients are applied
without a curved-area assignment. Compiled traversal through types, bodies
and private helpers requires their own edition's reduction and exhaustion,
excluding foreign witnesses and ModernLib. The pair `2^-m`, `2*2^-m` has a
vanishing gap and positive terms, but its ratio remains `1/2`; a Lean proof
rejects the unit-ratio conclusion without a uniform denominator bound.
The same harness now proves all four interior-positive edition clients apply
to the zero-base square patch, with no assigned curved area. Its fixed interior
rectangle at `c=1/2` has area `1/8`, with half-area `1/16`. Compiled traversal
requires each new client to use the derived denominator bound and the existing
ratio proof, as well as its own edition's reduction/exhaustion. The repaired
tail interface returns an actual offset; a delayed sequence has five initial
zeros yet supplies a positive term from the returned tail, and is rejected by
the all-index predicate. The shrinking-sequence control now rejects the
eventual-ratio conclusion for every offset, catching vacuous tail statements.
Earlier positive-cell and lower/upper-tail positivity controls are retained.
These controls share the kernel and rational definitions with the theorem;
they do not construct an area convention or the area of an arbitrary curved
figure. The zero-base mutual finite-area ratios are proved in the stated
interior-positive monotone rational domain.

`sector-difference-2026-10-07.lean` checks actual fan, connector and filled-strip
membership/exclusion, equivalent point displays, the strict half-plane bound
and unsigned areas for reversed/collapsed triangles. Its written rational-root
argument is not a Lean-certified exclusion of every matched parameter.
`motion-sampling-2026-10-07.lean` checks a displaced terminal connector and its
nonzero area, zero-time/inertial controls and the filled cover. Its compiled
dependency checks require each new historical client to use its own canonical
polygon, and each eventual sector-area client its own finite geometric proof;
foreign witnesses and ModernLib dependencies are rejected. Each new eventual
sector-difference client must also use its own triangle chain to derive
orientation and the proved FanDifference inclusion. The separate
full-turn union/multiplicity falsifier remains in `sector-unions-2026-10-07.lean`.
Each new assigned-full-cover-area client must additionally use its own
preceding sector-inclusion client, the proved terminal triangle square cover
and the finite square-union area construction. Concrete motion controls
check `K=19/16`, radius `19/32` at level 1, and full budgets `361/32` and
`361/64`, while retaining the explicitly noncentral control curve.
Each new mechanical/given-curve cover client must use its own preceding
mechanical/sample cover client, the derived radial collar bound and the
full-chart sector identification. Each conditional B-area client must use
its own preceding curve-cover client. Traversal includes types and helpers.

`triangle-exchange-2026-10-08.lean` checks finite simplex exit with signed
inserted coordinates, rejects an excessive scale and an invalid total, and
exercises independent, collinear, reversed radial order and coincident rays.
Its displaced one-cell difference point belongs to neither the mechanical
sector nor terminal connector; the derived cover therefore supplies actual
square membership. The general many-cell inclusion is checked separately.

`fan-difference-2026-10-08.lean` exercises the general geometric inclusion
with both strict orders of boundary-crossing cells, a collapsed first cell,
and a terminal-only point proved to lie outside every filled cell. The
symmetric form, nonmonotone intermediate radii and zero-group-weight
convexity are included. These shared-kernel controls do not assign an area
to the sector-union difference or the square-cover union.

`box-cover-area-2026-10-08.lean` checks the separate square-union area
construction under the explicit existing `TriangleContent.AreaRules`
translation-and-cut convention. Two overlapping unit-radius squares have
area `6` by a different vertical dissection, while their summed budget is
`8`; an assignment of area `8` is rejected. Duplicate squares have area `4`,
and zero-radius, negative-centre, closed-lower-edge, reversed-box and empty
cover controls are included. The general construction supplies the overlap
assignment and bound, and the motion client supplies vanishing cover areas
without motion or curved-area hypotheses. These controls share the kernel
and coordinate definitions; they do not prove a model of the convention,
subtraction-only sufficiency, or the actual mechanical/curve difference B.

`radial-triangle-cover-2026-10-08.lean` checks thin triangles with
`p=(2,1)`, `q=p+(0,2^-j)` and derived covering radius `4*2^-j`, including
all rational barycentric points, the upper vertex, origin, reversed vertex
order, a negative determinant, final cells and a collapsed origin triangle.
A displaced point rejects zero radius. Distinct joined-square groups force
both branches with points excluded from the other group. These are shared
kernel geometry controls, with no area-existence or curve-B conclusion.

`motion-curve-cover-2026-10-08.lean` checks the sharp collar-cell bound
`9/16`, equivalent representatives and a collapsed slope interval. For
`g(theta)=1+theta`, the nonlinear point `(9/8,9/64)` lies in the actual curve
sector outside its chord. Exact controls check the mechanical coefficient
`43/16`, collar coefficient `195/16`, combined coefficient `367/64`, and
budgets `134689/512` and `134689/1024`. Under acceleration `(0,2)`, the
given quadratic curve `(1+t,t+t²)` has terminal point `(5/4,5/16)` outside
its level-zero mechanical sector; the point belongs to the new cover and
rejects zero radius. The force is explicitly noncentral. This finite
quadratic control does not construct its full Conditions/RadialChart witness
or assert a Newton area law. The constructed square-cover areas are exercised
under the existing explicit translation-and-cut premise.
`historical-motion-area-2026-10-07.lean` exercises all three new historical
cover and conditional B-area clients on its already proved satisfiable
central inertial motion and full chart. B-area existence remains supplied.
These controls and the sequential Sol review share the rational definitions
and Lean kernel with the proof; neither establishes a model of AreaRules.

`area-domain-2026-10-08.lean` exercises the relative countermodel for the
unchanged `TriangleContent.AreaRules`. Both nested triangles retain their
areas `1/2` and `1`; points `(1/2,1)` and `(1/4,1/2)` belong to their
actual difference, which excludes the origin and has no minimum first
coordinate. The restricted convention therefore assigns that difference no
area. The existing separate `DifferenceAreaRules` does assign it `1/2`,
and assignment `1` is rejected. Assigned nonlinear radial sectors and actual
square-union areas are retained. A bounded line-segment predicate using only
the exact fraction display `0/1` at its left endpoint falsifies raw minimum
preservation under translation; representative invariance repairs the
restriction. Fresh sequential Sol controls exercise negative and collapsed
triangles, noncanonical translation, each minimum-union branch and an
incorrect empty-set area. These controls share the kernel and rational
definitions; the countermodel is relative to a supplied initial convention,
not a construction of one or a theorem that every historical B fails.

## Isolated source attestations

For Nine Chapters/FractionRules, verify each theorem's positive-input or
signed-whole domain against the separate 術 and commentary witnesses. Check
archive SHA-256, its ten S/R classifications and compiled dependency isolation.
The file uses core only; its presence at the ClassicsLib entry point must not
route existing historical proofs through its theorems. Source availability
and proof completion are separate, and no percentages increase for this work.
