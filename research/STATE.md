# Research state and open obligations

Updated 7 October 2026. This is the single maintained state/task file.
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
| Lemma III corollaries I–IV | Source-local area and boundary approximation chain. For concave increasing rational graph patches, two-sided secant contact and independent secant concavity now derive the supporting tangent cells, their meetings, a uniform continuity bound and two-sided chord/contact-tangent boundary approximation. The circumscribed tangent region encloses the curve and lies in the upper rectangle cover; assigned rational tangent-polygon areas have vanishing error through the edition's Corollary I | Arbitrary curves still use the older supplied supporting-cell interface. Tangent existence, other patch orientations and general patch decomposition remain open, as do existence of the curved/tangent-polygon areas, non-rational magnitudes and force-polygon correspondence. Rectangle covers are not staircase perimeters. No arclength conclusion |
| Laws' Corollary I | Endpoint constraints, unique intersection and central-cell composition; separate printed-edition derivations from supplied Law I inertia and calibrated Law II additive-change predicates | Mechanical laws are premises, not geometry theorems. Only 1713 explicitly cites Laws II/I in this proof; De Motu hypotheses and finite models remain witness-local |
| Laws' Corollaries V and VI | Separate 1687/1713 derivations from each edition's supplied Law I inertia and calibrated Law II predicates, for any family of bodies whose impulses depend only on their relative states. V: relative to a uniformly translated space every body has its resting-space state at each cell boundary. VI: common velocity changes add one shared motion to every body and leave all mutual states unchanged. NATP00090 states V as Lex 3, a law without proof | Vector addition of velocities and a shared time are explicit Galilean premises. Impulses at cell boundaries stand for collisions; contact geometry and continuous trajectories are not derived. Proposition II's second case and Proposition III do not yet use these theorems formally |
| Proposition I | Separate 1687/1713 finite constructions use their own Laws' Corollary I. Their new conditional given-motion reconstruction proves an assigned local swept-sector area equal to `T * det(initial position, initial velocity) / 2`, and comparison of two such areas from a shared initial time as their times. Finite force-polygon/sample agreement and slope-mesh exhaustion are derived from explicit quadratic local motion remainders, force comparison, short-window and finite bounds, with the supplied chart's positive ray scale. A supplied positive monotone rational radial chart describes the full curve image, beyond its samples. Its chord/curve symmetric difference has shrinking finite covers | Extend beyond the rational local chart and stated mechanical/regularity premises; preserve De Motu's own exhaustion route. Whole-edge/arbitrary-time force-polygon agreement and the actual between-region B for those mechanical polygons remain open. Rational curved areas and the partial area convention are supplied. No unrestricted historical Proposition I is certified |
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
line. The separately defined polygonal region under the lesser of the two
endpoint tangent heights contains the curved figure and lies in the upper
rectangle union. Both editions apply their own Corollary I to obtain area-error
decay for separately assigned rational areas, and their own Corollaries II–III
to obtain the chord and contact-tangent boundary limits.

The secant concavity/contact conditions are explicit editorial coordinate
regularity, not quoted Newton hypotheses. Their existence for an arbitrary
curve is not proved. The area convention and assigned curved/polygon areas
remain premises; the exact identification of the joined trace with the upper
boundary of the polygonal region is not yet formalized. Extend to the other
patch orientations and justify patch assembly before claiming the unrestricted
printed corollaries. De Motu retains its own unnumbered exhaustion route.

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

Controls: `motion-sampling-2026-10-07.lean` prescribes a quadratic curve under
a constant, explicitly noncentral acceleration and proves its nonzero quadratic
cell remainder, finite bounds and derived sample agreement without claiming
Newton's area law. `historical-motion-area-2026-10-07.lean` gives a
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

Last full verification: 7 October 2026, after the contact-tangent increment
and an independent sequential Sol review. All five builds, the 23 positive
controls, the harmonic reference/comparator, source hashes and whitespace
passed. The compiled checker verified 1,181 score comments and
6,911 project constants with no project axioms, sorry or primary modern
dependency. The corrupted comparator failed at its intended false equality.
The diagrams recover 79 source edges and 27 formal cross-file uses across 22
historical files. Archived Newton sources and exact Latin are unchanged by
this increment. The review found no defect within the stated rational patch
scope; it does not discharge the supplied area or mesh premises. Astra's review
covers the radial-sector increment (`3a2f5e3`, `b827902`) only.

Next extend the conditional rational local result to the remaining stage and
geometric scope. De Motu needs its own finite construction/exhaustion passage;
no printed Lemma III dependency is retrofitted. Derive whole-edge/arbitrary-
time polygon agreement and actual between-region covers for Newton's force
polygons. Existing shrinking collars concern the sampled-curve chords. Keep
area existence, general non-rational coordinates and winding/multiplicity
separate from this local area law. See [verification](VERIFICATION.md) and
[source/compiled-use diagrams](figures.md).
