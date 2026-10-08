# Research state and open obligations

Updated 8 October 2026. This is the single maintained state/task file.
Follow [the current handoff](HANDOFF-2026-10-06-REWORKED-SOURCES.md) and
[GOALS.md](GOALS.md). Previous session logs and task snapshots are in Git.
The historical-file refactor and source-only cleanup were committed and
pushed as `60180f2`; the user released the review hold.

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
| Lemma II | Exact equal-width gap, actual rectangle-union side-product areas under explicit partial area rules, derived enclosure/errors and unit ratios to a fixed positive assigned rational curved area; actual use of the edition's Lemma I | Existence of the geometric area convention and the curve's area remain premises; arbitrary non-rational areas and ratios of two varying areas require further treatment |
| Lemma III | Maximum-width exhaustion, actual use of Lemma II's geometric enclosure and Lemma I's contradiction; area errors and fixed-area unit ratios for unequal widths | Same area scope as Lemma II; mesh exhaustion must be established for the particular force polygons |
| Lemma III corollaries I–IV | Source-local area and boundary approximation chain. For concave increasing rational graph patches, two-sided secant contact and independent secant concavity derive the supporting tangent cells, their meetings, a uniform continuity bound and two-sided chord/contact-tangent boundary approximation. The joined trace equals the filled tangent polygon's vertical top, including shared endpoints, coincident lines and repeated nodes. Rectangle/triangle normalization, cut additivity and translation invariance now derive the actual finite polygon's trapezoid-sum area. Its error against an assigned curved area vanishes through the edition's Corollary I; no separate polygon-area assignment is needed in the constructed interface | Arbitrary curves still use the older supplied supporting-cell interface. Tangent existence, other patch orientations and general patch decomposition remain open, as do existence of the geometric area convention and curved area, non-rational magnitudes and force-polygon correspondence. Rectangle covers are not staircase perimeters. No arclength conclusion |
| Laws' Corollary I / De Motu Lemma 1 | Endpoint constraints, unique intersection and central-cell composition; separate printed-edition derivations from supplied Law I inertia and calibrated Law II additive-change predicates. NATP00090 now derives its own two endpoint constraints and independent-line intersection from its Lex 1 inertia and Lex 2 calibrated velocity difference; direct addition also covers degenerate directions and zero time | Mechanical laws are premises, not geometry theorems. Only 1713 explicitly cites both Laws II/I in this proof; NATP00090 cites Lex 2, and post-impulse inertia is an editorial interpretation of its Lex 1. Its literal M/AC label inconsistency is recorded. NATP00089 retains its own hypothesis/model scope |
| Laws' Corollaries V and VI | Separate 1687/1713 derivations from each edition's supplied Law I inertia and calibrated Law II predicates, for any family of bodies whose impulses depend only on their relative states. V: relative to a uniformly translated space every body has its resting-space state at each cell boundary. VI: common velocity changes add one shared motion to every body and leave all mutual states unchanged. NATP00090 states V as Lex 3, a law without proof | Vector addition of velocities and a shared time are explicit Galilean premises. Impulses at cell boundaries stand for collisions; contact geometry and continuous trajectories are not derived. Proposition II's second case and Proposition III do not yet use these theorems formally |
| Proposition I / De Motu Theorem 1 | NATP00090's finite recurrence uses its own Lemma 1 and Lex 1/2; the printed editions use their own Laws' Corollary I. All three now have conditional given-motion results assigning the actual local swept sector area `T * det(initial position, initial velocity) / 2`, with proportionality for two windows sharing their initial time. NATP00090 uses direct elementary exhaustion for its unnumbered passage; the printed editions use their own Lemmas III/I. Polygon/sample agreement and slope-mesh exhaustion are derived from explicit quadratic mechanical remainders, force comparison, a short window and finite bounds. A positive monotone rational radial chart describes the full curve image. Its chord/curve symmetric difference has shrinking finite covers. The NATP00090 area-law interface needs only triangle/cut area rules, without a rule for subtracting regions | Extend beyond the rational local chart and stated mechanical/regularity premises. NATP00089's hypothesis and limiting assertion remain separate from NATP00090's laws and reconstruction. Whole-edge/arbitrary-time force-polygon agreement and the actual between-region B for those mechanical polygons remain open. Rational curved areas and the partial area convention are supplied. No unrestricted historical Proposition I is certified |
| Mechanical polygon/sample-chord bridge | The actual symmetric difference of two positive ordered finite fans with a common start is proved to lie in the independent-parameter filled edge strips and terminal radial triangle. Internal connector triangles are eliminated through rational ray corridors. Existing motion premises enclose the strips in shrinking square covers; the terminal triangle has a derived unsigned area and vanishing bound. The chart and sample estimates derive the mechanical half-plane eventually. Separate NATP00090, 1687 and 1713 clients derive orientation from their own triangle chains and retain their own canonical polygons | Assigned difference/cover union areas and the actual curve's B remain open. No arbitrary-time curve agreement |
| Proposition II | Finite oriented-area converse, including unequal durations and uniformly moving centres | Vanishing-triangle/continuous-curve passage. Direction does not determine inward sense; unsigned areas and a vertex at the centre require separate treatment |
| Proposition III | Relative deflection and reference-history cancellation; finite converse application | Realized relative-orbit limit. No Law III, mass/force law or force/time-scale conclusion is derived |
| Proposition IV | Conditional finite circular sagitta comparison | Circle geometry, force interpretation and edition-specific ultimate ratios: 1687 uses Proposition II and Lemmas V/XI; 1713 uses Proposition II, Proposition I corollaries 2/4 and Lemma VII |
| Lemmas IX–XI support | Conditional quadratic/contact arithmetic and coefficient rearrangements in the owning historical files | Actual curved contact, mechanical velocity-area enclosure and variable-force comparisons; regularity/finite-curvature clauses stay edition-local |
| Lemma X corollaries | Separate 1687 Corollaries 1–2 and 1713 Corollaries 1–5 in ultimate-ratio form, each applying its edition's Lemma X reconstruction. Errors at proportional times share one positive ultimate coefficient (1); divided by force and squared time they are ultimately one positive calibration `k` (2, 3); 1713 Corollaries 4 and 5 solve Corollary 3's proportion for the force and for the squared time | Equal or force-proportional Lemma X coefficients are supplied premises, read from Law II. Similar figures and force-free places are not constructed, and the ultimate ratio of two varying errors is not formed. |

No complete historical Proposition I–IV proof is certified. These retained
results are finite, conditional or modern reconstructions in their stated
domains. There is no theorem-count or percentage completion metric.
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
This assigns no area to the covered difference or cover union and does not
yet prove the given curve's B.

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

The next obligation is to combine the proved mechanical/chord inclusion
with the existing curve/chord collar and justify the finite-union and
difference-area rules needed for actual B. A sum of square side products
is still a covering budget; it is not an assigned area of the union or
the covered difference. NATP00089's separate source-local chain,
other patch orientations and non-rational areas also remain open.

The mechanical/sample-chord increment derives whole-edge comparison for the
two finite polygons from the existing motion conditions. Their equal-parameter
edge points differ by at most `2*C*T*h`. Every actual matched interpolation
patch lies in a square centered at its left curve sample, of radius
`(V+3*C*T)*h`. The sum of the squares' side-product budgets is
`4*(V+3*C*T)^2*T*h`, which vanishes along the dyadic refinements. The actual
finite matched locus is proved to lie in that square union, including
equivalent rational point representatives. The budget counts overlaps; it
does not assign an area to the union. No centrality, radial chart, curved area
or new regularity premise is needed. Separate NATP00090, 1687 and 1713 clients
use their own canonical mechanical-polygon identity.

These covers and connector bounds are intermediaries required by Astra's
next-goal evaluation; the curve's between-region B remains open. The
sector-difference inclusion is now proved; adequate area rules are still
needed before inferring any assigned B bound. Astra's interface assessment flags
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
side-product budgets, not assigned areas. The public edge and patch theorems,
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

Last full verification: 8 October 2026, after the whole finite fan-difference
inclusion and three witness-local mechanical clients, with sequential Sol
controls and an Astra review. All five
builds, 30 positive controls, the harmonic reference/comparator, source hashes
and whitespace passed. The compiled checker verified 1,181 score comments
and 7,354 project constants with no project axioms, sorry or primary modern
dependency. The corrupted comparator failed at its intended false equality.
The diagrams recover 80 source edges and 27 formal cross-file uses across 22
historical files. Archived Newton sources and the transcribed Latin are
unchanged. New coordinate statements record their derivations without
historical textual attribution. Compiled witness-client controls traverse
types, bodies and private helpers, require each client's own canonical
polygon identity and each eventual sector-area client's own finite geometric
proof. The new difference clients must use their own triangle chain and the
proved FanDifference inclusion. Foreign witnesses and ModernLib are excluded.
Sol's retained adversarial controls force both crossing-index orders, a
collapsed cell and the terminal-only branch. Astra found no substantive
correction in the inclusion or clients, compiled the new controls and
confirmed closure of the finite geometric obligation in its stated domain.
This review shares the Lean kernel and supporting rational definitions.
Unrestricted curves, assigned mechanical sector-union difference area and
the actual curve's B remain open.

Next justify area bounds for the actual covered difference and combine the
proved mechanical/chord cover with the curve/chord collar. Astra's bounded
next target is to construct an assigned area of the finite square-cover
union, initially for nonnegative radius with squares wholly inside the
positive horizontal half-plane, and prove it is nonnegative and at most
the sum of the squares' side-product budgets. Derive translated-square
normalization and finite rational dissection from the existing partial
area rules. `DifferenceAreaRules` adds nested subtraction, not arbitrary
overlapping-union area or subadditivity; neither may be silently supplied.
The terminal triangle already has an assigned unsigned area and vanishing
bound. Later combination with the curve/chord collar remains explicit.
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
time polygon agreement and actual between-region covers for Newton's force
polygons. Existing assigned curve-collar areas concern sampled-curve chords;
the new mechanical/chord cover has no assigned difference area yet. Keep
area existence, general non-rational coordinates and winding/multiplicity
separate from this local area law. See [verification](VERIFICATION.md) and
[source/compiled-use diagrams](figures.md).
