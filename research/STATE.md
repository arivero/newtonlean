# Research state and open obligations

Updated 10 October 2026. This is the single maintained state/task file.
Follow [the current handoff](HANDOFF-2026-10-06-REWORKED-SOURCES.md) and
[GOALS.md](GOALS.md). Previous session logs and task snapshots are in Git.
The historical-file refactor and source-only cleanup were committed and
pushed as `60180f2`; the user released the review hold.

## Authorized core migration

The user selected Lean 4.34.1 on 10 October, retaining core/Std only and no
external packages. The toolchain-only compatibility stage preserves all
project theorem statements and names. The temporary bridge now proves the
roundtrip, equivalence/order/positivity correspondences and all requested
operation laws, including durationDifference sigma tau = tau - sigma.
Negation and time difference retain their definitions and names, relocated
to the common arithmetic module to avoid an import cycle. Existing proofs
do not use the new bridge. Next migrate clients bottom-up and remove
representative transport that equality makes redundant. Completion estimates
are reassessed and unchanged: this is encoding work, not a historical proof.
Core availability does not attest historical availability. The separate
[FractionRules](../ClassicsLib/NineChapters/FractionRules.lean) file now checks
ten Nine Chapters attestations (5 S, 5 R), using only core Rat/Nat/List.
Positive chapter-1 inputs and a separate Liu Hui commentary witness retain
the source limits; no existing Newton proof is routed through the file. Signed multiplication, general zero arithmetic and
signed order require their own exact passages before historical attribution. The open source audit includes Zhu Shijie's
算學啟蒙 (1299, ClassicsLib by the Chinese exception) and Brahmagupta (628,
BarrowLib); no exact passage for these additional operations was verified in
this increment. None is attributed to the Nine Chapters.
Representative-sensitive statements are a stop condition, not permission to
change their meaning silently. InertialControl.velocityBound/radius is a
confirmed instance: velocities (1/1,0) and (2/2,0) have the same rational value,
but at tolerance 1 their radii have values 1/2 and 1/3. Core Rat identifies
these velocities. A scratch Lean counterexample verifies the differing
radii. The user authorized normalized Rat numerators and a reproof of the
drift estimate on 10 October. Apply that choice when the ModernLib client
migrates; it changes the chosen witness explicitly, not the estimate's
conclusion. No local unreduced representation is required for this bound.
Frozen baseline outputs remain in scratch only.

The first Rat foundation increment supplies Rational.magnitudes and migrates
RationalExhaustion.le_of_enlargements to Rat. Its half-gap witness is still
necessary: a bare grind call does not instantiate the arbitrary positive
tolerance. Five call sites in CompletionGeometry, ScalarOrder, BoundedCuts
and SquareOuterContent convert explicitly through the bridge. No historical
statement or edition-local proof is changed.

FiniteCrossing now uses core Rat with no project imports and no warnings.
The rising, falling and unoriented finite crossing theorems retain their
mathematical meanings. FanRadial, RadialTriangleCover, FanCorridor and
FanDifference convert comparisons through the temporary bridge. The unused
chain_cover wrapper is removed; ordered_connector_bracket and between_split
are inlined, and the private le_total duplicate is replaced by core order
reasoning. These are four deleted helpers, not historical proof progress.
RationalMagnitudes remains a transitional module with its legacy Fraction
model; its remaining warnings are handled when that model migrates.

SimplexExit now uses core Rat with no project imports or warnings. Its
signed-coordinate facet-exit theorem and one shared below-candidate estimate
replace fourteen theorem declarations. Twelve helpers disappear: the core
total-order duplicate and eleven helpers handled inline by core arithmetic
and grind. A single grind with the available core multiplication facts does
not close the retained estimate, which is used for all three coordinates.
TriangleExchange converts inputs/results through the bridge; the signed
inserted coordinates, nonnegative residuals and facet conclusion are retained.
The bridge gains nonnegative_iff_toRat as its fourteenth temporary theorem.

Exhaustion's rational terminal-zero theorem now takes Rat, retaining its
nonnegative terminal value, vanishing-gap and terminal-comparison premises.
The unused zero_terminal_lower example is deleted; the scoped positive
controls still check inhabited terminal comparisons. The NATP00090 AreaLaw
caller converts its constant gap through the bridge without changing its
statement. RatMagnitudes contains the unchanged core model separately from
legacy Fraction; RationalExhaustion and Exhaustion therefore have no legacy
arithmetic import. LemmaI imports that legacy arithmetic explicitly until
its own migration. All five migrated common modules and their imports build
without any warnings; relocation earns no proof progress.

FiniteGrowth now represents finite product amplification by core Rat. Its
uniform bound and concatenation identity retain their meanings; eleven
named theorems replace nineteen. A core power duplicate, three inlined
cases/controls and four unused wrappers are removed. Both numeric controls
remain checked anonymous examples. FiniteFactorProducts and HarmonicUniform
adapt their direct calls through the bridge. The latter splits its four-factor
identity into two repeated blocks, avoiding grind's polynomial-step limit.
The migrated module builds without warnings. This earns no completion credit.

RationalTolerance now uses Rat, retaining the weak tolerance bound and
removing three named positivity/strict-control wrappers. Call sites convert
through the bridge and use core division order inline. A scratch proof checks
that eps / (C + 1) equals the old tolerance's rational value; normalized
representatives therefore change no bound. The module has no project imports
or warnings. Historical statements and completion estimates are unchanged.

RatUltimateScaling now proves positive output multiplication/division and
positive argument rescaling directly for Rat → Rat functions. A bounded,
sequential Astra review identified why the legacy higher-order API must remain
until its historical callers migrate together: normalized sampling loses
values at unreduced representatives. A scratch Lean example is zero on every
normalized Rat representative but one on 2/(2N) for every positive N; it also
distinguishes 1/2 from 2/4. These are checked representative computations;
the arbitrarily-small-input argument is the review's mathematical explanation,
not a claimed compiled limit countertheorem. Do not infer reverse transport of
arbitrary Fraction functions or add equivariance to historical premises.
The authorized coordinated domain change to Rat is still available. The three
new project derivations have no historical clients yet, add no historical
completion credit, and build without warnings. All six builds pass; existing
historical statements and axiom sets are unchanged.

The user added a deprecation-only cleanup before continuing Rat clients:
use each replacement named by Lean, edit with the patch tool, preserve
statements and counts, compare the theorem dump with Stage 0 and require
zero deprecation warnings in all six builds. All six builds now pass with
zero deprecations, down from 70. The 543 unused-simp warnings in 106 files
and five proposition-as-definition warnings are unchanged by this cleanup.
CheckReferences and the scope/graph harnesses also use the replacement names.
The original 4.34.1
snapshot's two additional unused-simp warnings disappeared with the migrated
RationalExhaustion proof. Remaining simp cleanup accompanies each module's
Rat migration, then one post-Stage-3 sweep; no warning suppression is allowed.
The toolchain-only commit 3237ff3 passed all six builds on 4.34.1. Its
2,427 source-declared project theorem names (including Reverse) and all
31 README own/proof/import counts matched the 4.19 baseline. Rendered type differences concern numeral/let/binder/projection
printing and a renamed core proof in a subtype argument. All 228 historical
axiom reports retain their axiom sets after normalizing generated-helper
names; 198 are source-declared historical theorems. Fewer compiler-generated
constants explain the lower environment size, not deletion of mathematics.

Optional user proposal, 10 October: after the core migration, consider an
isolated `BarrowLib/Algebra/PiuDiMeno.lean` with two Rat components and
Bombelli's 1572 multiplication/cubic example. Exact Italian passages and
archived witnesses are prerequisites. Cardano's 1545 chapter-37 irrational
example requires a supplied square root or an explicit not-encoded note;
Descartes's 1637 "imaginaires" is terminology only. Wallis's 1685 geometry
requires an exact statement match. No historical client imports this optional
support without a Newton passage; Newton's Arithmetica/De methodis witnesses
remain outside the current Proposition I–IV programme. No completion credit.

## Historical target

Proposition I comes first, then II, III and IV, separately for the De Motu
witnesses, 1687 and 1713. Read the exact Latin proof and its invoked results
in each historical Lean file. A source citation or unused import is not a
formal dependency.

The trajectory is given explicitly. Mechanical laws and needed regularity are
separate premises. Proposition I must prove **A**, swept-sector area proportional
to time. **B**, nonnegative area between polygon and curve, controls the
approximation where used. The position–velocity determinant is supporting
work. Neither A, B nor polygon/curve agreement is part of trajectory existence.

## What is proved and what remains

| Result or bridge | Retained checked result | Open historical obligation |
| --- | --- | --- |
| Lemma I | Separate 1687/1713 positive-terminal-difference contradictions, including an actual positive before-end time window; rational terminal-zero consequence | Terminal comparisons and approach premises are supplied; terminal values are not constructed. No general equality of objects is inferred from an unspecified difference |
| Lemma II | Exact equal-width gap, finite rectangle areas and exhaustion; edition-local Lemma I. Any assigned curved-area magnitude is approximated under explicit classical halving and area rules; a separate uniformly continuous graph construction removes monotonicity for absolute area exhaustion. Integer multiples now give all three mutual ultimate unit-ratio comparisons; an interior positive rectangle derives a lower bracket despite initial zero lower sums | General area/convention existence, arbitrary patches and non-rational coordinates remain open. Only the rational magnitude model is constructed; arbitrary-domain area assignments remain conditional. Full Eudoxian ratio calculus is outside the current encoding |
| Lemma III | Maximum-width exhaustion and the edition's Lemma II enclosure approximate any assigned area magnitude; its own Lemma I excludes a positive terminal gap. Integer multiples now give all three mutual unit-ratio comparisons on monotone graphs, including zero-base interior-positive patches. A separate uniform-continuity construction gives nonmonotone area exhaustion on all fine partitions | Same remaining area/coordinate scope as Lemma II; applications must establish mesh exhaustion for their force polygons. Exact finite ratio equality and full ratio calculus are not claimed |
| Lemma III corollaries I–IV | Source-local area and boundary approximation chain. Corollary I now also accepts any supplied area magnitude under explicit X.1 halving and geometric area rules, through its own Lemma III, now also for nonmonotone uniformly continuous nonnegative graphs. On monotone graphs it proves two-sided approach of explicit free staircase tops/vertical joins and their inclusion in the actual lower/upper rectangle unions. For concave increasing rational graph patches, two-sided secant contact and independent secant concavity derive the supporting tangent cells, their meetings, a uniform continuity bound and two-sided chord/contact-tangent boundary approximation. The joined trace equals the filled tangent polygon's vertical top, including shared endpoints, coincident lines and repeated nodes. Rectangle/triangle normalization, cut additivity and translation invariance derive the actual finite polygon's trapezoid-sum area. Its error against an assigned curved area vanishes through the edition's Corollary I; no separate polygon-area assignment is needed in the constructed interface | Arbitrary curves still use the older supplied supporting-cell interface. Tangent existence, other patch orientations and general patch decomposition remain open, as do existence of the geometric area convention and curved area, non-rational coordinates, full ratio calculus and force-polygon correspondence. Staircase traces omit fixed baseline/endpoint sides; no full closed-boundary or arclength claim |
| Laws' Corollary I / De Motu Lemma 1 | Endpoint constraints, unique intersection and central-cell composition; separate printed-edition derivations from supplied Law I inertia and calibrated Law II additive-change predicates. NATP00090 now derives its own two endpoint constraints and independent-line intersection from its Lex 1 inertia and Lex 2 calibrated velocity difference; direct addition also covers degenerate directions and zero time | Mechanical laws are premises, not geometry theorems. Only 1713 explicitly cites both Laws II/I in this proof; NATP00090 cites Lex 2, and post-impulse inertia is an editorial interpretation of its Lex 1. Its literal M/AC label inconsistency is recorded. NATP00089 retains its own hypothesis/model scope |
| Laws' Corollaries V and VI | Separate 1687/1713 derivations from each edition's supplied Law I inertia and calibrated Law II predicates, for any family of bodies whose impulses depend only on their relative states. V: relative to a uniformly translated space every body has its resting-space state at each cell boundary. VI: common velocity changes add one shared motion to every body and leave all mutual states unchanged. NATP00090 states V as Lex 3, a law without proof | Vector addition of velocities and a shared time are explicit Galilean premises. Impulses at cell boundaries stand for collisions; contact geometry and continuous trajectories are not derived. Proposition II's second case and Proposition III do not yet use these theorems formally |
| Proposition I / De Motu Theorem 1 | NATP00090's finite recurrence uses its own Lemma 1 and Lex 1/2; the printed editions use their own Laws' Corollary I. All three now have conditional given-motion results assigning the actual local swept sector area `T * det(initial position, initial velocity) / 2`, with proportionality for two windows sharing their initial time. NATP00090 uses direct elementary exhaustion for its unnumbered passage; the printed editions use their own Lemmas III/I. Polygon/sample agreement and slope-mesh exhaustion are derived from explicit quadratic mechanical remainders, force comparison, a short window and finite bounds. A positive monotone rational radial chart describes the full curve image. Its chord/curve symmetric difference has shrinking finite covers. The NATP00090 area-law interface needs only triangle/cut area rules, without a rule for subtracting regions | Extend beyond the rational local chart and stated mechanical/regularity premises. NATP00089's hypothesis and limiting assertion remain separate from NATP00090's laws and reconstruction. Whole-edge/arbitrary-time force-polygon agreement and existence of the actual between-region area for those mechanical polygons remain open. Rational curved areas and the partial area convention are supplied. No unrestricted historical Proposition I is certified |
| Mechanical polygon/given-curve bridge | The actual symmetric difference of two positive ordered finite fans with a common start lies in the independent-parameter filled edge strips and terminal radial triangle. Internal connector triangles are eliminated through rational ray corridors. Existing motion estimates enclose these and the full curve/chord collar in one finite square union. Under the existing explicit translation-and-cut area convention, finite dissection constructs its nonnegative assigned area, bounded by `8*W²/2^j` and vanishing along refinement. Separate NATP00090, 1687 and 1713 clients use their own triangle chains, canonical polygons and geometric inclusions. Any separately assigned rational areas of the actual mechanical/given-curve sector difference are nonnegative and vanish | Existence of the actual between-region area remains open. The subtraction-only convention is not silently strengthened. No arbitrary-time curve agreement, general patch assembly or unrestricted historical B |
| Proposition II | Finite oriented-area converse, including unequal durations and uniformly moving centres | Vanishing-triangle/continuous-curve passage. Direction does not determine inward sense; unsigned areas and a vertex at the centre require separate treatment |
| Proposition III | Relative deflection and reference-history cancellation; finite converse application | Realized relative-orbit limit. No Law III, mass/force law or force/time-scale conclusion is derived |
| Proposition IV | Conditional finite circular sagitta comparison | Circle geometry, force interpretation and edition-specific ultimate ratios: 1687 uses Proposition II and Lemmas V/XI; 1713 uses Proposition II, Proposition I corollaries 2/4 and Lemma VII |
| Lemmas IX–XI support | Conditional quadratic/contact arithmetic and coefficient rearrangements in the owning historical files | Actual curved contact, mechanical velocity-area enclosure and variable-force comparisons; regularity/finite-curvature clauses stay edition-local |
| Lemma X corollaries | Separate 1687 Corollaries 1–2 and 1713 Corollaries 1–5 in ultimate-ratio form, each applying its edition's Lemma X reconstruction. Errors at proportional times share one positive ultimate coefficient (1); divided by force and squared time they are ultimately one positive calibration `k` (2, 3); 1713 Corollaries 4 and 5 solve Corollary 3's proportion for the force and for the squared time | Equal or force-proportional Lemma X coefficients are supplied premises, read from Law II. Similar figures and force-free places are not constructed, and the ultimate ratio of two varying errors is not formed. |

No complete historical Proposition I–IV proof is certified. These retained
results are finite, conditional or modern reconstructions in their stated
domains. The [README](../README.md#proof-progress) gives user-requested rounded
remaining-work estimates for each historical file and witness: work done /
(work done + estimated remaining work). Its separate measured table records
source lines, declared theorems and distinct theorem counts in compiled proof
and import dependencies. These measurements inform the estimates; neither an
estimate nor a count certifies historical completion. The explicit obligations
here remain authoritative.
The requested modern-dependency score measures each anachronical proof's
dependency burden, not progress toward historical completion. Exact original-
language source coverage of the supporting libraries is still being checked;
known results are not attributed to their AI formalizers. New project
derivations are classified by their mathematical dependencies, rather than
their date of authorship.

## Retained construction and deferred applications

The general ModernLib construction uses regional force contracts, a calibrated
short window and explicit finite bounds. Actual, coarse and both shadow sample
locations are derived before force evaluation. Completed force values use
certified regional representatives; curve radii follow from the finite
invariant. The former whole-plane premise is removed. Confinement uses L1
coordinate bounds, not an established Euclidean Kepler force law.

Endpoint/prefix constructions, dyadic-time agreement, a local continuous
binary-time state map and whole-edge polygon control remain available.
General interior-time agreement, window gluing, arbitrary partition independence
and external real-time identification remain open. Active harmonic instances
and controls are retained; historical-file reachability alone does not decide
whether supporting work is useful.

`GeneralForceArea` proves local all-interval unsigned fan area
`abs(ell)*abs(elapsed)/2`, including reversal and zero cases. Fans count
multiplicity; ordinary sector-union area is not established. Actual matched
regions have canonical nonnegative square outer content with a proved geometric
bound and decay. Shared `BinaryLift`, polygon and matched-region geometry avoid
separate completion and alias proofs for each client.

`GivenTrajectoryArea` proves polygon identification, interval fan proportionality
and separate B under `Consistency`: independent rational curve samples,
candidate-arrival region membership, a local mechanical residual and shrinking
full-grid source budget. Area and polygon agreement are conclusions. Deriving
consistency from independent motion laws remains open. Its modern historical
wrappers stay below the five-line anachronical separator, along with the
completed rectangle and supporting-boundary applications.

Velocity/force secants, normalized second departure, tangent triangles and
harmonic potential increments remain modern support. Unrestricted difference
quotients, general radial potential steps and the centre-at-infinity time map
are deferred. The Euclidean Kepler 1/r² instance follows the general Proposition
I proof as an application. Weaker force classes need separate convergence and
uniqueness statements, with counterexamples where appropriate.

## Sources, diagnostics and immediate work

NATP00089 and NATP00090 retain separate revisions. Their area arguments do not
cite a numbered limiting lemma; do not give them the printed Lemma III citation.
LemmaI.lean houses the exact NATP00090 par12–13 Lemma 2 passage and a conditional
enclosing-ratio reconstruction of its unnumbered exhaustion step. This is an
editorial comparison with printed Lemma I, not De Motu's numbered Lemma 1 (motion
composition), and not a newly asserted dependency of its Theorem 1. NATP00089's
unnumbered terminal assertion remains with its Theorem 1 in AreaLaw.lean.
Proposed 1694 and 1726 remain comparison witnesses. Earliest H4 chronology,
direct C42 text and exact draft-folio identification remain source gaps.
The edited Rouse Ball witness and its limits are in [sources.md](sources.md).

The [action arguments](action-arguments/README.md) remain a separate diagnostic
layer. Positivity, finiteness, partition stability, system independence and
action rescaling are distinct tests. No universal constant or quantum premise
closes a historical proof.

## Current increment and next work

`UniformRectangles.exhaustion` removes monotonicity from conditional rectangular
area exhaustion of a nonnegative rational graph. Uniform continuity supplies
a local ordinate bound. Each cell's left sample gives lower height
`max(0,H-eps)` and upper height `H+eps`; their actual strip unions enclose the
figure and have constructed finite areas. The total gap is bounded by
`2*eps*(b-a)`. The explicit X.1 unit-halving premise selects eps so the gap
and both errors against any supplied `A : Q` are below each positive magnitude
tolerance, on every sufficiently fine partition. A shared finite enclosure
comparison is extracted from the older magnitude-error proof.

Both printed editions have separate Lemma II → Lemma III → Corollary I
clients of this construction. This is an editorial project extension of the
figure scope, not Newton's printed telescoping argument or a quoted continuity
hypothesis. Its compiled chain uses the same edition's new clients and shared
Barrow support; unlike the retained endpoint-gap proofs, this alternative
construction does not call Lemma I. The original exact Latin is preserved.
The control graph `|t-1/2|` decreases to zero and rises again, with proved
uniform continuity and actual shrinking dyadic partitions. An old endpoint
lower rectangle provably fails to lie below that graph. All six clients and
the nonvacuous fine-partition error tail compile without ModernLib use.

Remaining Lemma II–III work includes the broader ratio and explicit-boundary
scope, area/convention existence, non-rational coordinates and patch assembly.
Do not infer nonmonotone staircase convergence or unit ratios from this area
theorem. For the arithmetic foundation, the user's Euclid VII.19/Nine Chapters
source route is recorded in [BARROWLIB_BOUNDARY.md](BARROWLIB_BOUNDARY.md).
Exact passages are pending. Source relocation alone changes neither the
representation cost nor historical proof completion; alternatives must first
be compared on one bounded arithmetic client as described in
[PROOF_STRATEGY.md](PROOF_STRATEGY.md).

The user's classical comparison examples now live in ClassicsLib. Euclid
VII.31 supplies a prime divisor by finite descent; IX.20 proves a prime lies
outside any proposed finite list and supplies the numeric `n ≤ p` form.
Its finite product replaces the least common multiple in Euclid's original
construction, with that substitution recorded explicitly. The √2 example
excludes `a*a = 2*(b*b)` for natural or integer terms with nonzero denominator,
using parity and decreasing positive denominators. Aristotle's Greek at
Prior Analytics I.23, 41a26–27 attests the contradiction, not these complete
reconstructed steps. No real square root or geometric diagonal is constructed.
The Lean files pin and discuss the inspected mathlib routes. The primes route
uses classical arithmetic; the real √2 route uses rational-square criteria,
the inverse of a power order isomorphism and a Cauchy-completed real type.
The replacements use only Lean core and the displayed classical helpers.
This source inspection is distinct from a compiled mathlib dependency census.
The new compiled controls exclude later project libraries and exercise empty
and repeated prime collections, a composite product-plus-one, unreduced and
negative ratios, and the necessary zero-denominator exclusion.

The classical size comparison also prompted [PROOF_STRATEGY.md](PROOF_STRATEGY.md):
design from the historical target, reuse permitted foundations and accept
increments by the obligation discharged. Core arithmetic is excluded from
our project counts, while our rational geometry is included; aggregate file
counts are not individual proof sizes. The verification checklist now asks
for an explicit comparison of conclusions and remaining premises. Public Lean
skills were reviewed as sources of techniques, without installing packages
or adopting mathlib, sorry scaffolds or additional agent procedures.

The printed 1687/1713 Lemmas II and III now prove the mutual-ratio clause
for finite rectangle unions on a nonzero rational interval with a positive
starting ordinate. `MonotoneRectangles.lower_sum_base_bound` telescopes all
cell widths and proves `(b-a)*g(a) ≤ lowerSum` independently of the mesh.
Monotonicity then gives the same fixed positive bound for the upper sums.
`RectangleContent.varying_ratios_approach_one` bounds each absolute ratio
error by the absolute gap times the reciprocal of that fixed bound.
Positivity of both denominators is derived. Equal widths use
the owning edition's exact gap identity; unequal widths use that edition's
Lemma II reduction and its own maximum-width exhaustion. No curved-area
assignment or later reciprocal-limit theorem is used. The finite union areas
still use the unchanged explicit `RectangleContent.AreaRules`.

Exact controls give lower/upper areas `9/8` and `13/8` and mutual ratios
`9/13` and `13/9` for `g(x)=1+x²` on the two-cell unit interval, including
aliased endpoint displays. Repeated nodes, unequal cells, constant heights
and degenerate patches are exercised. A positive pair `L_m=2^-m`,
`U_m=2*2^-m` has a vanishing absolute gap but constant ratio `1/2`;
the Lean control rejects the conclusion that both ratios approach one. These
controls share the rational definitions and kernel. The zero-base case is
handled by the interior-rectangle argument below, allowing early lower sums
to vanish; general curved-area existence is still separate.
The finite prerequisite is proved in
`MonotoneRectangles.lower_sum_positive_of_positive_cell`: under the existing
monotonicity and nonnegative-base premises, one positive-width cell whose left
ordinate is positive makes the complete lower sum positive. The later
interior-rectangle proof supplies the uniform eventual denominator bound;
this positive-cell helper alone does not claim that bound.

`AreaDomain.relative_countermodel` settles a specific premise question
behind the remaining B-area obligation. From any supplied
`TriangleContent.AreaRules`, it constructs a convention satisfying all
original rules by retaining representative-invariant sets with an attained
minimum first coordinate, together with the empty set. Rectangles,
triangles of either orientation, translations and separated unions retain
these properties. Any already assigned positive radial sector also retains
its area, so the restriction need not remove the curved-sector input.

The nested triangles `O,(1,0),(1,1)` and `O,(1,0),(1,2)` retain areas
`1/2` and `1`, while their actual symmetric difference has no assigned
area in this convention. Every point of that difference has positive first
coordinate, and every proposed minimum admits a strictly smaller rational
point on the ray of slope `2`. This is a relative countermodel to uniform
difference-area existence from the current rules, conditional on an initial
supplied convention. It does not establish an initial area model or a
failure of Newton's physical or geometric claim. Under the separately stated
existing `DifferenceAreaRules`, the same nested difference has area `1/2`.
The two interfaces are not silently combined, and the nested repair does
not prove area existence for arbitrary mechanical/curve intersections.

`RadialCollarCover.triangle_collar_ball` derives a finite collar-cell bound.
For `a ≤ b` and `0 < R ≤ S`, a point in the radius-`S` triangle outside the
radius-`R` triangle has radial coordinates `R ≤ rho ≤ S`, `a ≤ t ≤ b`.
Its coordinate L1 distance from the lower left vertex is at most
`(S-R)*(1+abs(a)) + S*(b-a)`. Equivalent rational representatives and collapsed
slope intervals are included. No area or limiting theorem is used.

`MotionCurveCover` derives the radial increments from actual sampled-step
bounds and the slope widths from the existing motion estimates. Chart
monotonicity bounds the node radii by `g(r)`. Consequently the full curve/chord
collar is covered by the first group of existing mechanical-cover centres,
with radius `J*T/2^j`, where
`J=(V+C*T)*(1+abs(l)+abs(r)) + g(r)*slopeCoefficient(g(l),P,V,C,T)`.
Enlarging both groups to radius `W/2^j`, `W=K+J*T`, covers the actual
mechanical-polygon/given-curve sector symmetric difference eventually.
The full chart identifies the curve image over every rational time in
`[0,T]`; this set inclusion does not assert same-time polygon agreement.
The finite square union has constructed nonnegative assigned areas bounded
by `8*W²/2^j`, tending to zero. Areas are not identified with that budget.

Each of NATP00090, 1687 and 1713 has its own
`eventual_mechanical_curve_between_cover_areas`, using its own preceding
mechanical/sample inclusion and triangle chain. Each also has
`mechanical_between_area_approximation`: if rational areas of the actual
between-regions are separately assigned, they are nonnegative and vanish.
Existence of these B-area assignments is explicit, separate from trajectory
existence, and is not inferred from the outer covers. These results use the
existing `TriangleContent.AreaRules`; they do not merge it with
`DifferenceAreaRules` or strengthen the older area-law interfaces.

`RadialTriangleCover.terminal_triangle_square_cover` covers the terminal
triangle by squares centred along its first radial edge. If that endpoint
has coordinate L1 magnitude at most `R` and the endpoints differ by at most
`delta`, barycentric arithmetic and a finite crossing in the divided unit
interval give `2^j` covering squares of radius `delta + R/2^j`. No orientation,
half-plane, area convention or continuous intermediate-value theorem is used.
Collapsed triangles, reversed vertex order and terminal subdivision cells
are included.

`MotionSectorCover` derives these bounds from the existing mechanical cap
and terminal sample error. Its two groups of `2^j` squares cover the edge
strips and terminal triangle together. With
`K = (V+3*C*T)*T + 2*C*T² + R`, all use radius `K/2^j`, so their summed
side-product budget is `8*K²/2^j`. The finite square-union theorem below
constructs nonnegative assigned areas bounded by that budget and proves
their exhaustion. This is a larger geometric cover of the earlier
square-union/terminal-triangle cover; no area of that earlier union or the
covered difference is silently supplied.

Separate NATP00090, 1687 and 1713
`eventual_mechanical_sector_difference_cover_areas` clients apply their own
preceding sector-inclusion proofs, which derive orientation from their own
triangle chains and use their own canonical polygons. Each derives an
eventual full cover with vanishing assigned area. The new clients explicitly
supply `TriangleContent.AreaRules`; their older area interfaces are unchanged.
The library's `assigned_difference_bound` only bounds a separately assigned
sector-difference area, and its name and hypotheses retain that distinction.
Existence of the actual given curve's between-region area remains open;
the new increment above closes its geometric cover and conditional decay.

`BoxCoverArea.cover_area` constructs assigned areas of actual finite unions
of closed rational axis-parallel boxes from the existing
`TriangleContent.AreaRules`. Adding one box cuts the old union into four
exterior parts and its intersection with that box. Replacing the middle
part by the whole box constructs the enlarged union. The nonnegative area
of the old intersection proves that the increase is at most the box's
side product; overlapping-union area and subadditivity are conclusions,
not supplied rules. Reversed boxes are empty; collapsed boxes, shared
boundaries and boxes crossing either axis are included.

`square_cover_area` applies this to the actual `ConvexCover.SquareCover`
point set. `MotionSampling.sampled_chord_cover_areas` constructs its
nonnegative assigned areas, bounds them by the existing budgets and proves
they vanish. It needs only nonnegative `C,T,V` and the explicit area
convention, without a mechanical or curved-area assignment. Translation
invariance remains a supplied geometric premise already used for tangent
polygons; no historical interface is strengthened by this increment.
The weaker `RadialSector.DifferenceAreaRules`-only derivation remains open.
Subtracting two closed base-axis rectangles omits the lower edge of a
translated closed box, so that particular construction does not suffice.
This does not establish insufficiency of the weaker convention.

`FanDifference.symmetric_difference_cover` now proves the whole finite
geometric inclusion: two fans sharing their initial vertex, with positive
horizontal coordinates and nonnegative consecutive determinants, have their
actual sector-union symmetric difference in the filled paired-edge strips
or final radial connector triangle. No area or desired inclusion is supplied.
The proof intersects a fixed rational ray with the boundary edges. On the
intervening connectors, ordered slopes derive opposite height signs and hence
rational intersection points. Convexity of the independent-parameter filled
cells and finite interval induction cover the radial interval between the
boundary crossings. Intermediate radii may reverse order. If the ray extends
beyond one fan's final slope, its final connector supplies the remaining cap.
Internal origin triangles are never added to the cover budget.

The checked scope includes equal slopes, coincident vertices, zero group
weights and the vacuous zero-cell case. Exact controls force both strict
orders of crossing-cell indices, a collapsed first cell, and a terminal-only
point outside every filled cell. They share the rational definitions and
Lean kernel with the proof, rather than independently certifying those layers.
`MotionSampling` combines the inclusion with its existing square cover and
derives sample orientation from the chart. Each historical witness's new
eventual mechanical-sector-difference client derives mechanical orientation
from its own finite triangle chain and uses its own canonical polygon
identity. The existing square and terminal area budgets exhaust separately.
The geometric inclusion itself assigns no area. The square-union area is
now constructed above under the explicit translation-and-cut convention;
the larger combined square cover has an assigned vanishing area as described
above. The covered difference and given curve's B still have no constructed
assigned area; conditional decay of any separately assigned B areas is now
proved above.

Finite triangle exchange is now proved in `TriangleExchange`: for positive
horizontal A,Q with nonnegative orientation, a point of triangle O,A,Q is
covered by O,A,P, A,P,Q or O,P,Q. The positive-determinant
case derives the inserted point's signed rational coordinates. A finite
simplex-exit construction keeps all residual weights nonnegative and makes
one zero, including exterior inserted points. Positive horizontal original
vertices with nonnegative orientation also admit collinear and coincident
ray cases, derived as ordered radial segments. The translated triangle has
derived convex parameters and square enclosure; neither area rules nor a
sector-difference inclusion is a premise.

For a common initial vertex, triangle exchange now derives the actual
one-cell sector-difference inclusion in the existing square or the endpoint
radial connector. `MotionSampling.initial_cell_difference_cover` applies
this to the first mechanical/sample cell from its motion conditions and
explicit local orientation/positivity. The separate ray-corridor proof above
extends the geometric conclusion through all cells. Exact controls include signed/exterior coordinates,
collinear and coincident rays, and a displaced endpoint whose difference
point lies outside both the mechanical sector and terminal connector, forcing
the square-cover branch. A fresh sequential Sol review supplied an exterior
inserted point with unnormalized coordinates that lies in neither origin
cone, forcing the translated triangle branch; that control is retained.
The triangle-exchange theorem remains supporting finite geometry.

The filled-strip/terminal-connector increment enlarges the finite edge patch
to use independent rational parameters on its two edges. The same radius
and summed square budget below enclose this larger actual locus. The old
equal-parameter matched patch remains valid for its stated comparison but
does not suffice for the proposed sector-difference inclusion: a rational
point in the larger strip can require an irrational matched parameter. The
new geometric controls check the point's fan membership, exclusion from the
other fan and terminal connector, and filled-strip membership. The rational-
root exclusion itself is a written argument, not a kernel-checked theorem.

Triangle normalization and vertex exchange derive the unsigned area of any
terminal radial connector, including reversed and collapsed cases. The
mechanical position cap `R` and terminal sample error give area at most
`R*(2*C*T*h)`, which vanishes. This uses the derived mechanical cap because
the supplied curve-position bounds omit the terminal sample. The full chart's
positive lower radius and the shrinking sample error also derive a common
positive half-plane for every mechanical vertex eventually. Each witness's
own finite geometric sector theorem then gives its actual polygon-union
area without an additional half-plane premise at that client. The geometric
area convention, centrality, initial orientation and motion/chart premises
remain explicit; this is a conditional rational reconstruction.

The full mechanical/chord cover and curve/chord collar are now combined
under the existing translation-and-cut convention above. Construction of
the actual between-region area remains open. The sum of square side
products bounds the assigned square-union area; it need not equal that area
and assigns no area to an arbitrary covered difference. NATP00089's separate
source-local chain, other patch orientations and non-rational areas remain open.

The mechanical/sample-chord increment derives whole-edge comparison for the
two finite polygons from the existing motion conditions. Their equal-parameter
edge points differ by at most `2*C*T*h`. Every actual matched interpolation
patch lies in a square centered at its left curve sample, of radius
`(V+3*C*T)*h`. The sum of the squares' side-product budgets is
`4*(V+3*C*T)^2*T*h`, which vanishes along the dyadic refinements. The actual
finite matched locus is proved to lie in that square union, including
equivalent rational point representatives. The budget counts overlaps;
the new finite dissection assigns the union an area at most that budget.
No centrality, radial chart, curved area or new regularity premise is needed
for this square-union result; the area convention remains explicit.
Separate NATP00090, 1687 and 1713 clients
use their own canonical mechanical-polygon identity.

These covers and connector bounds are intermediaries required by Astra's
next-goal evaluation. The mechanical/given-curve sector-difference inclusion
and an assigned vanishing full-cover area are now proved under the existing
translation-and-cut convention, including the curved collar. Conditional
decay of separately assigned B areas is proved; existence of the actual
difference area remains open.
Astra's interface assessment flags
that the dyadic motion premises and full-image chart leave the temporal order
of points between samples unconstrained. Same-time arbitrary-rational curve
agreement remains open and needs independently justified temporal premises.
No such agreement is inferred from this finite cover.

The NATP00090 exhaustion increment proves a conditional area law for the
full image of a given rational-time curve. Its own Lex 1/2 and Lemma 1
finite triangle chain gives the canonical mechanical fan area. The separate
quadratic motion-remainder and force/bound premises derive polygon/sample
agreement; the full radial chart and those same premises derive the slope
mesh. Elementary strip arithmetic exhausts the geometric chord-area error.
The fixed discrepancy between the assigned curved area and the finite area
formula is bounded by the sum of two derived vanishing errors, so elementary
exhaustion makes it zero. A further theorem proves cross-product area/time
proportionality for two admissible windows sharing their initial time.

The new NATP00090 proof uses its own finite chain and BarrowLib arithmetic,
with no printed-edition theorem as a formal dependency. Triangle/cut area
rules suffice for this area-law interface; no rule for subtracting regions
is needed. Its force comparison, quadratic remainder, short window, finite
bounds and full positive monotone rational chart are explicit editorial
regularity premises, not hypotheses quoted from the unnumbered assertion.
The geometric area convention and assigned curved area remain supplied.
NATP00089's hypothesis and limiting assertion, unrestricted/non-rational
curves, patch assembly and the actual mechanical-polygon between-region B
remain open.

The NATP00090 motion-composition increment derives its Lemma 1 from its own
Lex 1 and Lex 2 premises. Lex 1 supplies unimpeded uniform drift at nonnegative
rational times. Lex 2 supplies the velocity difference generated by a
calibrated directed impulse on one fixed body. Finite cancellation derives
addition, then the two transverse endpoint constraints and their unique
intersection for independent directions. A separate direct addition proof
includes parallel, opposite and zero impulses and zero time; it does not
claim uniqueness of degenerate endpoint lines. The Latin is preserved:
par11 labels the force along AC as M although its setup associates M with AB
and N with AC. The vector roles are an explicit editorial interpretation of
that inconsistent label and the symmetric argument.

NATP00090's Theorem 1 now uses this law-driven Lemma 1 in the actual sampled
impulse-then-drift recurrence. The two-triangle step and finite induction
derive equal signed doubled triangle areas. Elementary dissection then gives
the ordinary local sector-union area as elapsed time times the initial areal
product divided by two, under explicit area rules, nonnegative orientation
and a strict common positive half-plane. These finite conclusions supply
neither polygon/curve agreement nor a curved-area limit. They use no
printed-edition law or limiting lemma. NATP00089's revised hypothesis and
its existing finite models remain separate.

The contact-tangent increment of 7 October advances the printed Lemma III
Corollaries III–IV. Proposition I explicitly invokes Corollary IV in each
printed edition's limiting passage. `TangentContact`
represents a concave increasing rational graph by its own finite secant slopes
and their two-sided contact values. It does not assume tangent support,
intersections, rectangle enclosure, uniform continuity, boundary convergence
or area-error decay. Those conclusions are derived, with endpoint contact
one-sided and repeated partition nodes allowed. The contact slope at the left
endpoint bounds the graph throughout the patch and supplies the continuity
modulus. Every point of the joined tangent trace lies on an endpoint contact
line. Finite interpolation now proves that this trace is exactly the vertical
top of the filled polygonal region under the lesser of the two endpoint
tangent heights. This identification includes coincident lines, repeated nodes
and equivalent rational representatives. Partition order proves that boundary
points have maximal height even across different cells. Every region point
lies vertically below a trace point at the same abscissa. The region contains
the curved figure and lies in the upper rectangle union. Both editions apply
their own Corollary I to obtain area-error decay, and their own Corollaries
II–III to obtain the chord and contact-tangent boundary limits.

The finite tangent-polygon area is now constructed from an explicit elementary
area convention. `TriangleContent.AreaRules` extends the existing rectangle,
triangle and cut rules by translation invariance. A rectangle and a translated
right triangle dissect each increasing affine subgraph and derive its
width-times-mean-height area, including zero slopes and zero widths. Each
actual tangent cell is split at a constructed meeting into two such subgraphs;
vertical partition cuts add their areas. Both printed Corollary III sections
use this derived area, removing their separate polygon-area assignment.

The secant concavity/contact conditions are explicit editorial coordinate
regularity, not quoted Newton hypotheses. Their existence for an arbitrary
curve is not proved. The area convention and assigned curved area remain
premises; existence of that convention on general figures is not constructed.
The trace/region identity is finite rational geometry;
it is not a claim about a topological boundary in a completed plane. Extend
to the other patch orientations and justify patch assembly before claiming
the unrestricted printed corollaries. De Motu retains its own unnumbered
exhaustion route.

The laws-and-lemmas increment of 7 October adds primary proofs of Laws'
Corollaries V and VI and of Lemma X's missing corollaries. BarrowLib's
`CommonMotion` proves that common initial motion and common velocity changes
superpose on a finite impulse-then-drift system without changing its relative
states. Each edition's Corollaries V and VI apply it with that edition's Law I
and Law II predicates; Laws I/II are now formal dependencies of both. The
NATP00090 witness of Corollary V is Lex 3, revised from "Hypoth", and has no
proof. `UltimateScaling` adds division by a fixed positive magnitude and a
fixed time proportion to ultimate ratios; the Lemma X corollaries use them
with each edition's Lemma X reconstruction, and 1713 Corollaries 4 and 5 now
formally use Corollary 3. Next, Proposition II's second case and Proposition III should
use Corollaries V and VI in their own finite steps.

The motion-sampling increment derives finite force-polygon/sample agreement
from an independent quadratic local mechanical remainder, and the sampled
curve's slope mesh from displacement and a positive ray-scale lower bound.
Each printed edition's conditional local area law then uses its own Laws'
Corollary I/equal-triangle chain and Lemmas III/I. Its conclusion is the
assigned actual swept-sector area `T * det(initial position, initial
velocity) / 2`; a further theorem compares two windows sharing their initial
time as their elapsed times.

`MotionSampling.Conditions` contains only finite force comparison, a quadratic
cell residual, a short window and force/curve bounds. The separately supplied
`RadialChart` represents the full curve image in both directions and its own
equal-time samples; the chart is `(x,y)=(g(t),g(t)*t)`, with `t=y/x` the slope
and `g(t)` the positive x-coordinate. `sweptSector` is defined from every
rational-time point of the given curve in the window, including times between
samples. Neither structure supplies polygon agreement, shrinking mesh or an
area law. The partial area convention and any assigned rational curved area
remain explicit; general area existence is not constructed. The force
comparison is a whole-plane premise; forces singular at the centre need a
regional version available to the primary chain.

Controls: `demotu-composition-2026-10-07.lean` supplies concrete NATP00090
law witnesses for affine drift and vector impulse addition. Its full-step
central construction has arrivals `(2,1)` and `(0,1)` with both doubled
triangle areas `2`. Its half-step construction has arrivals `(2,1/2)` and
`(3/2,7/8)` with doubled area `1`; the two-cell ordinary union has area `1`
under explicit elementary area rules and derived half-plane/orientation
conditions. A noncentral impulse gives `(3,2)` and changes the doubled area
to `1`. Further controls cover zero time, dependent vectors and equivalent
rational representatives. These finite controls do not supply a continuous
curve-limit passage.

`demotu-exhaustion-2026-10-07.lean` checks a constant-radius partition with
widths `0`, `1/16` and `3/16`, gap `0` and chord area `1/8`. The inertial
curve `(1,t)` has swept-sector area `1/8` at time `1/4` and `1/16` at time
`1/8`, derived separately from the triangle convention. For the latter
window the control constructs the motion conditions and full chart, uses
NATP00090's new area theorem to identify any assigned area, and rejects the
incorrect area `1/8`. A compiled dependency traversal checks that the new
finite fan, geometric exhaustion, area law and comparison reach no
printed-edition declaration, including through types and private helpers.
These controls retain the explicit elementary area convention.

`motion-sampling-2026-10-07.lean` prescribes a quadratic curve under
a constant, explicitly noncentral acceleration and proves its nonzero quadratic
cell remainder, finite bounds and derived sample agreement without claiming
Newton's area law. Its new matched-edge controls distinguish the mechanical
endpoint `(0,1/4)` from the given sample `(1/16,1/4)` and derive midpoint
distance `1/32`, rejecting a zero-discrepancy claim. For `C=1`, `V=2` and
`T=1/4`, the covering radii are `11/16` and `11/32`, and the summed budgets
are `121/64` and `121/128` for the first two refinements. These are derived
side-product budgets; the new union theorem bounds assigned cover areas by
them rather than identifying them with those areas. The public edge and patch theorems,
finite set inclusion and budget exhaustion are exercised, with endpoint and
equivalent interpolation fractions, a final cell, zero time and a positive-
time inertial cell with zero edge discrepancy for every interpolation
parameter. `historical-motion-area-2026-10-07.lean` gives a
positive-time inertial curve, a full chart, satisfiable mechanical premises and
an actual swept-sector area from the triangle convention, then exercises both
printed editions. Earlier controls retain a nonlinear curve point outside its
chord, a shrinking collar of the actual symmetric difference, and the
complete-turn counterexample in `sector-unions-2026-10-07.lean`, where the fan
sum grows while the union stays fixed: consecutive positive determinants alone
cannot justify unrestricted union identification.
`laws-corollaries-v-vi-2026-10-07.lean` instantiates Corollaries V and VI
with a two-body spring impulse; a resistance measured in the resting space
breaks Corollary V, and collinear relativistic composition changes the velocity
differences that its "ex hypothesi" step keeps fixed.
`lemma10-corollaries-2026-10-07.lean` satisfies the Lemma X premises for `c t²`
and `c t² + t³` and shows that normalizing by the wrong force fails.
`tangent-contact-2026-10-07.lean` proves the contact and concavity premises
for `g(x)=4-x²` on `[-2,-1]`. Its endpoint tangents meet at `(-3/2,2)`,
above the curve value `7/4` and chord value `3/2`. A line through both
endpoints with slope `3` fails tangent contact. The control also checks a
repeated node, the literal tangent-region enclosure and both editions'
corollaries for arbitrary shrinking partitions.
`tangent-boundary-2026-10-07.lean` checks the lesser tangent heights `1` at
`x=-7/4` and `5/2` at `x=-5/4`, and excludes the higher tangent at each point.
Its quadratic trace controls retain an explicit contact patch. A separate
constant-height patch is constructed in this control; it checks coincident
lines, maximal height across different cells at a shared endpoint and at a
repeated node, and both directions of the vertical-top identity. The inverse
control starts from region membership and maximal height proved directly for
the flat figure. Both printed editions' polygon-boundary and perimeter
interfaces are exercised under the stated shrinking-mesh premise.
`tangent-area-2026-10-07.lean` checks the quadratic tangent polygon's two
trapezoids, with areas `1/2` and `5/4`, and its derived total `7/4`, distinct
from the chord region's `3/2`. It also checks the chosen meeting and finite
polygon sum, a flat cell of area `1`, a repeated-node cell of area `0`, and
zero-width and zero-slope triangles. These area controls retain the explicit
elementary area convention and contact patch; the nonlinear patch's existence
is proved in the earlier contact control. Both printed constructed-area
interfaces retain the curved-area and shrinking-mesh premises.

`box-cover-area-2026-10-08.lean` independently dissects the union of the
unit-radius squares centred at `(0,0)` and `(1,0)` into two vertically
separated rectangles of areas `2` and `4`. Any assigned union area is thus
`6`; the general construction supplies an assignment bounded by `8`, and
an assignment of `8` is rejected. Duplicate squares have area `4`, and the
controls include zero radius, negative centres, a closed lower edge,
reversed boxes, the empty cover and the motion client's area exhaustion.
A sequential Sol review found no missing hypothesis or circularity in
the five-part induction. This review and these different dissections share
the Lean kernel and supporting rational definitions; they do not construct
a model of the area convention.

`radial-triangle-cover-2026-10-08.lean` exercises the thin triangle
`p=(2,1)`, `q=p+(0,2^-j)` with derived covering radius `4*2^-j`.
It checks arbitrary barycentric points, reversed vertex order, a second
vertex below `p`, the origin, final subdivision cells and a collapsed
triangle. Distinct joined-square groups force both branches. Zero radius
rejects the displaced upper vertex. The existing noncentral motion control
gives `K=19/16`, radius `19/32` at level 1 and full budgets `361/32` and
`361/64`; it now exercises both geometric enclosure branches and the
constructed assigned-cover-area exhaustion. A sequential Sol review found
no hidden inclusion or area premise in the full-cover proof and checked
its radius and count algebra. New compiled witness controls require each
area client to use its own preceding sector-inclusion theorem, the proved
terminal-triangle cover and the finite square-union area construction.

`motion-curve-cover-2026-10-08.lean` checks a sharp finite collar bound
`9/16`, equivalent representatives and a collapsed slope interval. For
`g(theta)=1+theta`, `(9/8,9/64)` is a genuine curve-sector point outside
its one-cell chord. The exact combined coefficient is `367/64`, with
budgets `134689/512` and `134689/1024`. Under the explicitly noncentral
force `(0,2)`, the quadratic curve `(1+t,t+t²)` has terminal point
`(5/4,5/16)` outside its level-zero mechanical sector. That point lies in
the new cover and rejects zero radius. This finite control does not
construct the quadratic curve's full Conditions/RadialChart witness.
The historical inertial control supplies satisfiable central motion and
full chart premises for all three new witness-local cover and conditional
B-area clients. The latter controls retain B-area existence explicitly.
A sequential Sol review found no hidden desired inclusion or B-area
premise in the new library. It and these controls share the rational
definitions and Lean kernel; they do not construct a model of AreaRules.

`area-domain-2026-10-08.lean` exercises the retained triangle areas, actual
difference points at scales `1/2` and `1/4`, origin exclusion and missing
minimum. The separate subtraction convention gives area `1/2` and rejects
area `1`. Nonlinear radial-sector assignments and square-cover assignments
survive the restriction. The bounded representative-sensitive line test
shows why minimum attainment alone is not preserved by raw translation.
A fresh sequential Sol review found no defect and compiled distinct negative
and collapsed triangle, noncanonical translation, union-branch and false-area
controls, now retained in the same harness. The review and controls share
the rational definitions and Lean kernel; initial convention existence is
still an explicit input.

Last full verification: 10 October 2026, after the nonmonotone rectangular
area-exhaustion extension of Lemmas II/III and Corollary I. All five builds,
all 40 positive scope harnesses
(including the harmonic reference/comparator), source hashes and whitespace
passed. The compiled checker verified the README measurements, 1,181 score
comments and 7,993 project constants with no project axioms, sorry or primary
modern dependency. The corrupted comparator failed at its intended false equality;
a corrupted finite upper-height comparison also failed at its intended claim.
The diagrams recover 80 source edges and 27 formal cross-file uses across 22
historical files. Archived Newton sources and the transcribed Latin are
unchanged. New coordinate statements record their derivations without
historical textual attribution. Compiled witness-client controls traverse
types, bodies and private helpers, require each client's own canonical
polygon identity and each eventual sector-area client's own finite geometric
proof. The new difference clients must use their own triangle chain and the
proved FanDifference inclusion. The curve-cover clients additionally require
their own mechanical/sample client, the derived collar-cell bound and full
given-curve sector identification; the conditional B-area clients require
their own curve-cover client. Foreign witnesses and ModernLib are excluded.
The eight mutual-ratio clients must use their own edition's reduction and
gap exhaustion, with the same foreign-witness and ModernLib exclusions.
The four interior-positive clients additionally traverse the derived fixed
rectangle denominator bound and the existing mutual-ratio proof.
The two staircase clients additionally require their own Corollary I cover,
the node/sandwich estimates and all six new finite inclusions; their traversal
excludes foreign witnesses and every ModernLib-owned constant.
A sequential Sol review found no defect in the new denominator/ratio argument
and compiled an independent disposable proof extracting original-index
positivity and an epsilon bound from the returned tail. It made no repository
edits. The review and retained controls share the rational definitions and
Lean kernel; the supplied geometric area convention remains an input.
Sol's retained fan-inclusion controls force both crossing-index orders, a
collapsed cell and the terminal-only branch. Astra's preceding review of
the fan-difference increment, committed as `4db8758`, found no substantive
correction in the inclusion or clients, compiled the new controls and
confirmed closure of the finite geometric obligation in its stated domain.
This review shares the Lean kernel and supporting rational definitions.
Unrestricted curves and construction of actual mechanical/curve difference
areas remain open. The new conditional B-area decay is separate from Astra's
earlier reviewed fan-difference increment.

The zero-base Lemma II–III ratio obligation is now proved for nonnegative
rational monotone patches with a positive ordinate at `a≤c<b`, under the
existing explicit rectangle-area rules. The rectangle `[c,b]×[0,g(c)]` lies
below each upper cover; its positive area `R` and the vanishing upper/lower
gap derive the uniform eventual bound `R/2` on both sums. Both printed
editions use their own exhaustion proof and their own Lemma II reduction to
derive mutual ratios on an actual tail; initial lower sums may vanish.
The earlier tail statement's `∃ M, ∀ hNM : N≤M, ...` permitted an unusable
index. It is replaced by `∃ N, MutualRatiosOne (L(N+·)) (U(N+·))`, reusing the
existing ratio proof rather than duplicating its calculation. The harness
extracts a positive term after five initial zeros, applies all four new
clients to the square patch, checks its rectangle half-area `1/16`, and rejects
unit ratios for shrinking sequences with constant ratio `1/2` even after any
tail restriction. The earlier finite/tail positivity results remain available.
No curved area is assigned in this argument and no new axiom is introduced.
General curved-area existence, arbitrary patches and non-rational coordinates
remain open. Lemma III Corollary I now replaces the filled-cover surrogate
with explicit free horizontal tops and vertical joins of both rectangle
constructions. Every sampled left node lies on both traces; every trace point
lies in its endpoint box. The edition's own cover estimate and the existing
node approximation therefore give two-sided approach by a finite sandwich.
Both traces are proved to lie in their actual rectangle unions. The lower
trace includes only internal joins: a final rise to `g b` would lie above the
last lower rectangle, as the one-cell identity-graph control demonstrates.
The upper trace includes its initial partial side. Fixed baseline and
remaining endpoint sides are omitted; no full topological perimeter is
claimed. The new harness realizes a nonzero dyadic graph example, checks
omitted-endpoint approximation, repeated/aliased nodes, flat graphs and a
collapsed interval, and excludes filled-box interior points from both traces.
Continuity and mesh remain supplied; no curved area is assigned in the new
boundary argument. Its eight named support/client declarations are explicit
project derivations, not new historical quotations or priority claims.
The assigned-area magnitude restriction is now removed conditionally in both
printed editions' Lemmas II/III and Corollary I. `MagnitudeContent` pulls the
supplied general-magnitude area convention back to rational assignments,
reusing the actual finite rectangle proofs. The assigned curved area `A : Q`
need not lie in the rational image. Euclid X.1's exact-halves closing sentence
supports the visible `unit_halves_exhaust` premise for comparable area
magnitudes; it transfers the proved rational gap exhaustion to that domain.
Addition and comparison give both area-error bounds, and each edition's own
Lemma I excludes a positive supplied terminal gap. No area assignment or
convergence conclusion is built into the new magnitude rules.
The rational rules and the adapter for the existing partial area convention
compile. The new harness realizes nonzero dyadic graph partitions and checks
both editions with arbitrary assigned `A`, an unreduced rational display,
a zero-height patch and constant-gap/infinitesimal falsifiers. Compiled
traversal requires each edition's enclosure, gap proof, Lemma I and the
classical halving field, excluding foreign witnesses and ModernLib.
One bounded sequential Sol review found no blocking issue in the pullback,
comparison proof or X.1 specialization; it shares the source/model context
and is not an independent kernel. Only a rational magnitude realization
is constructed. General curved-area existence, non-rational coordinates and
arbitrary patch assembly remain open. The
current Proposition I area law still uses its older rational area interface.
[Greek source companions](../docs/classics/euclid-X1.md) distinguish the
classical premise from these eleven project-derived theorem declarations.
The assigned-area unit-ratio conclusion is now proved for both editions of
Lemmas II/III. For each fixed positive integer pair `n<m`, both cross
comparisons hold eventually for each of lower/upper, lower/assigned and
upper/assigned area. Actual repeated addition defines the multiples; weak
addition compatibility and strict preservation of rational comparisons are
explicit supplied laws with a rational realization. The shared argument
uses the already derived interior-rectangle lower bracket and a sufficiently
small finite rational gap. No ratio-limit hypothesis or rationality of the
assigned magnitude is supplied. The four clients use their own edition's
enclosure and exhaustion. Ten new named declarations comprise six shared
derivations (two private) and four historical clients.
The extended magnitude harness checks all four clients on the nonzero dyadic
identity graph, whose first lower sum is zero, and extracts an actual tail
comparison. Equal positive constants pass; zero/zero, constant 1:2 and two
shrinking areas in ratio 1:2 fail. The latter's absolute gap is proved to
vanish, demonstrating why positivity control matters. Compiled traversal
requires the actual comparison derivation and compatibility laws and excludes
foreign witnesses/ModernLib. A bounded sequential Sol review found no invalid
implication. The tests and review share the rational definitions and kernel.
[Euclid V.2/V.5](../docs/classics/euclid-V.md) supply comparison language,
not a sequence-limit theorem. Full V.5 finite ratio equality, a general ratio
calculus and a nonrational magnitude model are not constructed; abstract
`positive A` is not inferred from the interface's separate order relation.
Existence of the actual between-region area remains a separate obligation:
the relative countermodel rules out inferring arbitrary difference assignments
uniformly from the present translation-and-cut interface. The full
mechanical/given-curve cover and conditional decay of separately assigned B
areas are proved; constructed assigned areas belong to the enclosing square
unions. A constructive treatment of the actual difference needs an explicitly
justified area domain and operations.
The finite square-union construction
uses translation and cuts; the original `DifferenceAreaRules`-only target
remains open, including initially positive-half-plane squares. Neither
subtraction-only sufficiency nor insufficiency is established.
The mechanical
half-plane and sample orientation are derived eventually; each witness's
triangle chain derives mechanical orientation from centrality and the
nonnegative initial areal product. Those mechanical and chart premises
remain explicit. Keep NATP00089's
hypothesis and limiting assertion
separate from the NATP00090 law-driven reconstruction; no printed Lemma III
dependency is retrofitted. Extend the conditional rational local result to other patch
orientations and their assembly. Keep curved-area existence
separate from the finite polygon construction. Derive whole-edge/arbitrary-
time polygon agreement where required. Existing assigned curve-collar areas
concern sampled-curve chords; the new mechanical/given-curve cover has no
constructed actual difference area yet. Keep
area existence, general non-rational coordinates and winding/multiplicity
separate from this local area law. See [verification](VERIFICATION.md) and
[source/compiled-use diagrams](figures.md).
