# Theorem cascade and provenance

This note records the detailed meaning of the theorem counts in the README.
The counts are produced from the compiled Lean environment by
`research/CheckReferences.lean`; they are not a count of historical
propositions and they are not additive across rows.

The mathematical snapshot includes the nonmonotone rectangular-exhaustion,
mutual-ratio, free-staircase and matched-family extensions of 10 October 2026.
The README records why the reassessed Lemma II/III estimates remain 80% and
Corollary I remains 75% after the matched-family proof. It keeps the progress
estimates and compact measurements; this file explains
the kinds of result, their sources and the provenance coverage of the
dependencies actually used.

The Lean 4.34.1 toolchain-only commit 3237ff3 preserved the named theorem
cascades of caf90de and their provenance classifications. Core types and lemmas
are encoding infrastructure, excluded from these project-only counts and
M/H scores. This exclusion does not certify historical availability. Exact
source attestations and domain qualifications remain independent obligations.
No completion estimate changes for the migration.

The temporary bridge has fourteen P encoding-correspondence theorems in
RationalMagnitudes: toRat_ofRat, equiv_iff_toRat, lt_iff_toRat, le_iff_toRat,
positive_iff_toRat, toRat_add, toRat_mul, toRat_half, toRat_ofInt,
toRat_quotient, toRat_abs, toRat_negF, toRat_durationDifference and
nonnegative_iff_toRat.
Their exact statements and checked derivations are their provenance;
no historical source or new mathematical priority is claimed. Adding the
unused bridge left proof trees and M/H scores unchanged; converted callers
now acquire its actual dependencies. Import trees include its temporary
availability. Migration removes the bridge after clients switch to Rat.

The first Rat foundation increment migrates le_of_enlargements from the
Fraction namespace to Rational and qualifies it as P: its source is the exact
statement and half-gap derivation in RationalExhaustion. Core Rat realizes
Magnitudes without additional named theorems. Five legacy callers use bridge
conversions, temporarily increasing their actual project dependencies.

FiniteCrossing's three retained induction theorems now use core Rat without
project arithmetic imports. They are P: their original finite derivations
are in the file and claim no historical textual match or priority. The
unused chain_cover wrapper is deleted; ordered_connector_bracket and
between_split are inlined, and le_total is a removed core-order duplicate.
Fan geometry retains Fraction temporarily and converts comparison premises
explicitly, preserving their meaning.

SimplexExit retains two P declarations over core Rat: the signed barycentric
facet-exit theorem and the below-candidate estimate shared by three
coordinates. Their exact finite derivation remains their provenance. Twelve
old helpers are deleted: one core-order duplicate and eleven inlined helpers.
TriangleExchange uses the temporary bridge without changing its region
conclusion or excluding signed coordinates of the inserted vertex.

Exhaustion.rational_terminal_zero is a P reconstruction over Rat of the same
ordered-difference implication; its explicit premises remain unchanged.
The unused zero_terminal_lower instance is deleted. The core Magnitudes Rat
model moves unchanged to RatMagnitudes, separating migrated clients from
legacy Fraction imports without adding a theorem or changing provenance.

FiniteGrowth's uniform_amplification and amplification_append are now P
derivations over core Rat. Their exact finite statements and checked proofs
are in the module; no historical attribution or priority is claimed. Eight
named helpers disappear: denominator_power_add is a core duplicate,
amplification_empty is inlined, the two numeric controls remain anonymous
examples, and four unused wrappers are removed. Its direct legacy callers
convert with the bridge. Historical theorem statements remain unchanged.

RationalTolerance retains factor_delta_weak as a P finite derivation over
core Rat, with its exact statement and proof in the module. The denominator
positivity, tolerance positivity and strict-control wrappers are removed;
their uses close inline with core arithmetic. A scratch proof checks that
the new tolerance has exactly the old rational value. No historical textual
match or mathematical priority is claimed for this reconstruction.

RatUltimateScaling adds three P derivations: positive multiplication, division
and rescaling of the vanishing argument for arbitrary Rat-valued functions.
Their exact statements and checked proofs are their provenance, without a
historical attribution or priority claim. The legacy Fraction API is retained
until its historical callers migrate together: normalized sampling forgets
values at unreduced representatives, so there is no reverse bridge for an
arbitrary Fraction-valued function. Existing proof trees and M/H scores are
unchanged by this additive API; import trees include its three declarations.

FiniteSequenceGap.finite_gap is now a P finite induction over Rat distances,
parameterized by the state carrier rather than importing coordinate geometry.
Its exact statement and proof give project provenance, without a historical
attribution or priority claim. All four legacy callers convert their distance
values through the bridge; their state algorithms and theorem statements are
unchanged. No theorem is added or deleted in this increment. Its smaller
imports do not yet imply smaller client cascades because conversions remain.

RationalIntervals now contains only the core Rat midpoint definition. Its six
old U declarations are removed: half_equiv is redundant equality transport;
half_le, half_double, midpoint_between and the two midpoint gap identities
close inline with core arithmetic. No new theorem is added. Legacy state and
partition callers retain the original unreduced midpoint expression exactly;
only their comparison proofs use the bridge until their domains migrate.
The removed declarations had no verified historical provenance classification.

FiniteAccumulation's active scalar-power kernel now uses core Rat powers.
Its constant_budget_power_bound, shared power induction and temporary
finite-power value correspondence are P: the exact statements and
checked finite derivations give their provenance, without historical textual
attribution or priority claims. The nonnegativity duplicate is replaced by
Rat.pow_nonneg; FiniteRecurrence's redundant correspondence wrapper is deleted.
The final actual_uniform_error and cross_actual_uniform_error statements and
all historical theorem types remain unchanged. Actual state recurrences still
use their original representatives. FiniteAccumulation still awaits full
migration beyond this scalar kernel.

FiniteRecurrence now contains sourceBudget and two P bounds over core Rat,
without legacy imports or warnings. Their exact statements and finite checked
derivations give their provenance. The existing shared power induction moves
from FiniteAccumulation to Common/FinitePowers.one_le_power; the power value
bridge moves to FinitePower.toRat_fpower. These are relocations/renamings, not
additional theorem declarations. Six old U helpers disappear: fpower_congr
is redundant transport, fpower_add and fpower_integer_blocks are core-power
duplicates, one_le_fpower and fpower_prefix_le close inline with the shared
power induction and core facts, and sourceBudget_nonnegative is unused.
FinitePower adds one P temporary legacy_sourceBudget_two_count adapter used
by the still-legacy state modules. Net named-theorem reduction: five.
Its normalized Fraction outputs are numerical bounds only. A scratch
induction verifies their values against the original source-budget recurrence
for arbitrary signed inputs; positivity/lower-bound premises remain explicit
in the bounding theorems. No historical completion credit or textual match.

There are three different quantities:

- **Own theorems** are named theorem declarations in the file or library,
  including private helpers. Definitions, examples and compiler-generated
  equation lemmas are excluded.
- **Proof tree** is the distinct set of project theorems reached by traversing
  the types, definitions, proof bodies and private helpers of every declaration
  in the file. A shared theorem is counted once.
- **Import tree** is the distinct set of project theorems available in the
  file's compiled transitive imports. It includes theorems that the file does
  not use, including available library theorems. The proof tree measures
  actual dependencies; the import tree measures availability.

The current compiled cascade (10 October, with Nine Chapters attestation and temporary Rat bridge) is:

| Entry | Own | Proof tree | Import tree |
| --- | ---: | ---: | ---: |
| `AreaLaw.lean` | 73 | 880 | 1822 |
| `CompositionOfMotions.lean` | 13 | 48 | 183 |
| `LawI.lean` | 0 | 0 | 111 |
| `LawII.lean` | 0 | 0 | 97 |
| `LawsCorollaryV.lean` | 4 | 45 | 138 |
| `LawsCorollaryVI.lean` | 4 | 33 | 138 |
| `LemmaI.lean` | 7 | 18 | 91 |
| `LemmaII.lean` | 30 | 151 | 396 |
| `LemmaIII.lean` | 22 | 195 | 515 |
| `LemmaIII/CorollaryI.lean` | 14 | 158 | 529 |
| `LemmaIII/CorollaryII.lean` | 2 | 70 | 531 |
| `LemmaIII/CorollaryIII.lean` | 10 | 213 | 665 |
| `LemmaIII/CorollaryIV.lean` | 12 | 471 | 1395 |
| `LemmaX.lean` | 4 | 14 | 81 |
| `LemmaX/CorollaryI.lean` | 2 | 14 | 91 |
| `LemmaX/CorollaryII.lean` | 4 | 24 | 93 |
| `LemmaX/CorollaryIII.lean` | 1 | 20 | 94 |
| `LemmaX/CorollaryIV.lean` | 2 | 23 | 96 |
| `LemmaX/CorollaryV.lean` | 2 | 23 | 96 |
| `PropositionII.lean` | 0 | 0 | 28 |
| `PropositionIII.lean` | 0 | 0 | 45 |
| `PropositionIV.lean` | 0 | 0 | 78 |
| `ClassicsLib/NineChapters/FractionRules.lean` | 10 | 10 | 10 |
| `ClassicsLib` | 26 | 26 | 36 |
| `BarrowLib` | 985 | 985 | 985 |
| `ModernLib` | 1157 | 1491 | 1679 |

The README additionally lists line counts and the individual classical files.
Reproduce the compiled measurements and check the README with:

```sh
NEWTON_PRINT_THEOREM_COUNTS=1 lake env lean research/CheckReferences.lean
NEWTON_CHECK_README_COUNTS=1 lake env lean research/CheckReferences.lean
```

## Provenance within each actual proof cascade

These columns partition **theorem declarations**, using the same distinct
nodes as the proof-tree column above. They include the file's own theorems
and the library theorems actually reached through types, definitions, proof
bodies and private helpers. They exclude unused imports.

- **S — source match:** the represented result is matched to an exact
  original-language statement. This does not certify that the formal proof
  reproduces the source's proof word for word.
- **R — source-related reconstruction:** an inspected source motivates the
  result, but its coordinates, restricted domain, explicit limiting premises
  or reformulation require qualification. This is kept separate from an
  exact statement match.
- **P — internally derived support:** the exact statement and checked
  derivation or concrete control are presented here. This identifies the
  provenance of this formulation, without claiming novelty or transferring
  a known result's authorship to its formalizer.
- **U — unverified in this census:** the declaration has not received one
  of the preceding theorem-level classifications. It may already have a
  source comment. It is neither presumed unsourced nor counted as authored
  here merely because its Lean proof was written here.

For every row, **S + R + P + U = proof tree**. The reviewed groups are
identified below; classifications outside those groups remain U. In
particular, S=0 means that this review has established no exact statement
match in that cascade, rather than that the cascade has no historical
source. Source witnesses for every historical file remain in the next table.

| File or library | S | R | P | U | Proof tree |
| --- | ---: | ---: | ---: | ---: | ---: |
| `AreaLaw.lean` | 0 | 6 | 23 | 851 | 880 |
| `CompositionOfMotions.lean` | 0 | 0 | 0 | 48 | 48 |
| `LawI.lean` | 0 | 0 | 0 | 0 | 0 |
| `LawII.lean` | 0 | 0 | 0 | 0 | 0 |
| `LawsCorollaryV.lean` | 0 | 0 | 0 | 45 | 45 |
| `LawsCorollaryVI.lean` | 0 | 0 | 0 | 33 | 33 |
| `LemmaI.lean` | 0 | 7 | 0 | 11 | 18 |
| `LemmaII.lean` | 0 | 20 | 49 | 82 | 151 |
| `LemmaIII.lean` | 0 | 18 | 53 | 124 | 195 |
| `LemmaIII/CorollaryI.lean` | 0 | 12 | 53 | 93 | 158 |
| `LemmaIII/CorollaryII.lean` | 0 | 2 | 0 | 68 | 70 |
| `LemmaIII/CorollaryIII.lean` | 0 | 10 | 10 | 193 | 213 |
| `LemmaIII/CorollaryIV.lean` | 0 | 2 | 19 | 450 | 471 |
| `LemmaX.lean` | 0 | 0 | 0 | 14 | 14 |
| `LemmaX/CorollaryI.lean` | 0 | 0 | 0 | 14 | 14 |
| `LemmaX/CorollaryII.lean` | 0 | 0 | 0 | 24 | 24 |
| `LemmaX/CorollaryIII.lean` | 0 | 0 | 0 | 20 | 20 |
| `LemmaX/CorollaryIV.lean` | 0 | 0 | 0 | 23 | 23 |
| `LemmaX/CorollaryV.lean` | 0 | 0 | 0 | 23 | 23 |
| `PropositionII.lean` | 0 | 0 | 0 | 0 | 0 |
| `PropositionIII.lean` | 0 | 0 | 0 | 0 | 0 |
| `PropositionIV.lean` | 0 | 0 | 0 | 0 | 0 |
| `ClassicsLib/Aristotle/SquareRootTwo.lean` | 0 | 2 | 2 | 0 | 4 |
| `ClassicsLib/Euclid/FiniteLattice.lean` | 0 | 2 | 4 | 0 | 6 |
| `ClassicsLib/Euclid/PropositionI37.lean` | 0 | 1 | 0 | 0 | 1 |
| `ClassicsLib/Euclid/PropositionI38.lean` | 0 | 1 | 0 | 0 | 1 |
| `ClassicsLib/Euclid/PropositionIX20.lean` | 1 | 3 | 2 | 0 | 6 |
| `ClassicsLib/Euclid/PropositionVII31.lean` | 0 | 1 | 0 | 0 | 1 |
| `ClassicsLib/NineChapters/FractionRules.lean` | 5 | 5 | 0 | 0 | 10 |
| `ClassicsLib` | 6 | 12 | 8 | 0 | 26 |
| `BarrowLib` | 0 | 0 | 75 | 910 | 985 |
| `ModernLib` | 0 | 2 | 22 | 1467 | 1491 |

Across the whole loaded project environment, deduplicating rather than
adding these overlapping rows, this bounded review classifies **172 of 2374
theorems: 6 S, 49 R and 117 P; 2202 remain U**. This measures provenance-review
coverage, not proof completeness, novelty or a library's historical class.
Wrapped scratch output had left the Corollary III and IV provenance rows stale;
they now use unwrapped output and agree with their measured proof-tree totals.
This is a reporting correction, not additional mathematical progress.
The large U counts expose the remaining attribution work. They do not
invalidate the compiled proofs.

The zero proof trees of Laws I/II and Propositions II–IV also need care:
supplied-law predicates and source-only declarations do not count as named
theorems. Their nonzero import trees describe available support, rather than
a source-local proof.

## What kind of result each file contains

The links below lead to the exact Latin, witness URLs, proof correspondence
and formal statements. A witness section is a source unit, not a theorem
count. The rational models and supplied premises qualify the conclusions;
they do not inherit the full scope of a historical sentence automatically.

| File | Kind and scope of the checked result | Exact witness sections |
| --- | --- | --- |
| [AreaLaw](NewtonLimitDynamics/Historical/AreaLaw.lean) | Finite equal-area triangles and conditional assigned swept-sector laws under mechanical, area and chart premises; modern constructions are separate. | 4: NATP00089, NATP00090, 1687, 1713 |
| [CompositionOfMotions](NewtonLimitDynamics/Historical/CompositionOfMotions.lean) | Finite parallelogram endpoint geometry; rational-time motion composition from the witness's supplied mechanical laws. | 4: NATP00089, NATP00090, 1687, 1713 |
| [LawI](NewtonLimitDynamics/Historical/LawI.lean) | Supplied rectilinear inertial-motion predicate; no proof of a mechanical law is claimed. | 3: NATP00090, 1687, 1713 |
| [LawII](NewtonLimitDynamics/Historical/LawII.lean) | Supplied calibrated impulse/change predicate for a fixed body. | 3: NATP00090, 1687, 1713 |
| [LawsCorollaryV](NewtonLimitDynamics/Historical/LawsCorollaryV.lean) | Relative-state preservation at finite cell boundaries under shared time and relative-state impulse rules. The manuscript statement is a supplied law. | 3: NATP00090, 1687, 1713 |
| [LawsCorollaryVI](NewtonLimitDynamics/Historical/LawsCorollaryVI.lean) | Common calibrated changes preserve mutual states at cell boundaries; continuous forcing and absolute-state force rules are outside the model. | 2: 1687, 1713 |
| [LemmaI](NewtonLimitDynamics/Historical/LemmaI.lean) | Ordered exhaustion contradiction with explicit approach and terminal-comparison premises; manuscript enclosing-ratio step kept separate. | 3: 1687, 1713, NATP00090 |
| [LemmaII](NewtonLimitDynamics/Historical/LemmaII.lean) | Equal-width rectangle areas, gap exhaustion and all three mutual ultimate unit-ratio comparisons for an arbitrary assigned area magnitude, with a geometrically derived positive interior bracket. Integer multiples use explicit compatibility laws; absolute errors use X.1 halving. A separate uniform-continuity construction gives nonmonotone area exhaustion and all three multiple comparisons for every sufficiently small height tolerance and every fine partition, using a constructed positive rectangle. Coordinates/sums stay rational. | 2: 1687, 1713 |
| [LemmaIII](NewtonLimitDynamics/Historical/LemmaIII.lean) | Unequal-width counterparts using the same edition's Lemmas I/II, including arbitrary assigned-magnitude errors and all three integer-multiple unit-ratio comparisons; shrinking mesh is supplied and modern completion is separate. Its own Lemma II also supplies nonmonotone graph-area exhaustion and multiple-ratio comparisons. | 2: 1687, 1713 |
| [LemmaIII Corollary I](NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean) | Error decay for any supplied area magnitude under X.1 halving/area rules, and two-sided approximation of explicit free staircase tops/internal joins. Both now cover nonmonotone uniformly continuous nonnegative rational graphs. Shrinking mesh and height errors give boundary approximation and actual-union membership; area enclosure additionally needs the fine mesh–height relation. Fixed sides are omitted. | 2: 1687, 1713 |
| [LemmaIII Corollary II](NewtonLimitDynamics/Historical/LemmaIII/CorollaryII.lean) | Two-sided rational chord approximation; no area or arclength conclusion. | 2: 1687, 1713 |
| [LemmaIII Corollary III](NewtonLimitDynamics/Historical/LemmaIII/CorollaryIII.lean) | Supporting-tangent geometry and actual finite polygon area for concave increasing rational patches, with contact and area premises; tangent existence is not proved. | 2: 1687, 1713 |
| [LemmaIII Corollary IV](NewtonLimitDynamics/Historical/LemmaIII/CorollaryIV.lean) | Chord and tangent upper-boundary approximation in the stated rational domain; modern completed-curve results are separate. | 2: 1687, 1713 |
| [LemmaX](NewtonLimitDynamics/Historical/LemmaX.lean) | Conditional initial-time quadratic normalization from supplied limiting contact and mechanical enclosures; force identification remains supplied. | 2: 1687, 1713 |
| [LemmaX Corollary I](NewtonLimitDynamics/Historical/LemmaX/CorollaryI.lean) | Two errors share a normalized ultimate value under a common coefficient and proportional-time premises; their mutual ratio is not formed. | 2: 1687, 1713 |
| [LemmaX Corollary II](NewtonLimitDynamics/Historical/LemmaX/CorollaryII.lean) | Force/time-square normalization with a supplied common force calibration. | 2: 1687, 1713 |
| [LemmaX Corollary III](NewtonLimitDynamics/Historical/LemmaX/CorollaryIII.lean) | Applies that edition's Corollary II normalization to an arbitrary space with the supplied coefficient. | 1: 1713 |
| [LemmaX Corollary IV](NewtonLimitDynamics/Historical/LemmaX/CorollaryIV.lean) | Finite coefficient algebra and ultimate force normalization through Corollary III. | 1: 1713 |
| [LemmaX Corollary V](NewtonLimitDynamics/Historical/LemmaX/CorollaryV.lean) | Finite coefficient algebra and ultimate time-square normalization through Corollary III. | 1: 1713 |
| [PropositionII](NewtonLimitDynamics/Historical/PropositionII.lean) | Source correspondence and dependency statements; no source-local theorem yet. | 2: 1687, 1713 |
| [PropositionIII](NewtonLimitDynamics/Historical/PropositionIII.lean) | Source correspondence and dependency statements; no source-local theorem yet. | 2: 1687, 1713 |
| [PropositionIV](NewtonLimitDynamics/Historical/PropositionIV.lean) | Source correspondence and edition-specific limit obligations; imported modern finite sagitta support is not an edition-specific proof. | 2: 1687, 1713 |

Three files mix primary and anachronical theorem declarations: `AreaLaw`
has 57 primary and 16 anachronical, `LemmaIII` has 18 and 2, and its
`CorollaryIV` has 6 and 6. These are section counts, checked against their own
theorem totals; the compiled reference checker separately verifies dependency
taint. Their whole-file proof trees include both sections, so those aggregate
sizes should not be read as the cost of a primary proof alone. Importing a
modern module does not itself constitute using a modern theorem.

## Premises that theorem counts do not measure

A structure field or theorem argument can carry mathematical content without
being a named theorem or a Lean `axiom` declaration. The compiled axiom check
does not discharge such a premise. These are the important examples in the
current cascades:

| Cascade | Supplied input | What the checked proof establishes |
| --- | --- | --- |
| Lemma I | [Magnitudes](BarrowLib/Common/Quadratic.lean), `VanishingDifference`, `TerminalLower`; positive duration in the before-end version | The ordered contradiction; rational terminal zero when nonnegativity is supplied. No terminal object is constructed. |
| Lemmas II/III and area corollaries | [AreaRules](BarrowLib/Polygon/RectangleContent.lean): partial `HasArea`, rectangle normalization, vertical-cut additivity, congruence and monotonicity; shrinking mesh; a separate `HasArea` premise when a curved area is used | Finite rectangle areas and their geometric enclosures, gap exhaustion, and the stated conditional error/ratio conclusions. General curved-area existence is outside these results. |
| Assigned-magnitude extension | [MagnitudeContent.AreaRules and Rules](BarrowLib/Polygon/MagnitudeContent.lean): partial area convention, order/addition/rational embedding, positive unit and the sourced `unit_halves_exhaust` premise | The rational pullback reuses finite rectangle geometry. Exhaustion transfers to the supplied domain and gives comparison error bounds for arbitrary assigned `A : Q`. No nonrational model, curved-area existence or full ratio calculus is constructed. |
| Nonmonotone rectangular exhaustion | [UniformOn](BarrowLib/Polygon/RationalBoundary.lean), a nonnegative rational graph, ordered interval, explicit magnitude/area rules and a supplied curved-area assignment | Constructs clipped cell heights and actual enclosing strip unions on every sufficiently fine partition; total gap and both errors fall below each positive magnitude tolerance. The separate ratio and free-boundary extensions have their own premises. No extrema, monotone decomposition or area existence is supplied. |
| Nonmonotone free staircases | Uniform continuity, nonnegative graph and height errors, shrinking mesh and errors | Both clipped left-sample traces approach the graph in both directions and lie in their actual rectangle unions. No area assignment or monotonicity is used. Graph enclosure requires an additional mesh–height relation; fixed sides and full topological perimeter are omitted. |
| Matched nonmonotone rectangle family | Uniform continuity, nonnegative graph, positive vanishing height errors, any vanishing mesh, explicit area rules and curved-area assignment | Strictly increasing indices pair selected partitions with `eps m`, deriving enclosure at every step, a vanishing rational gap, assigned-area error decay and free-edge approach on that same family. Classical choice gives existential indices. Neither nested refinement nor full perimeter is inferred. |
| Assigned-area unit ratios | [MultipleRules](BarrowLib/Polygon/MagnitudeContent.lean): weak addition compatibility in the other addend and strict preservation of rational comparisons; an interior positive ordinate, geometric area rules and a supplied curved-area assignment | Actual integer multiples give both comparisons for each fixed `0<n<m`, for all three pairs of areas. The positive bracket is derived from an actual interior rectangle. No ratio convergence premise is supplied; full V.5 finite equality, general ratio calculus and a separate abstract `positive A` conclusion are outside this statement. |
| Boundary corollaries | [UniformOn](BarrowLib/Polygon/RationalBoundary.lean), shrinking mesh, and supporting/contact data where needed | Two-sided approximation of the stated traces. Tangent existence and arclength are not inferred. |
| Motion composition and laws' corollaries | [InertialMotion](NewtonLimitDynamics/Historical/LawI.lean), [AdditiveImpulse / CalibratedChange](NewtonLimitDynamics/Historical/LawII.lean), shared time and the displayed update rules | Endpoint geometry and finite motion consequences under those laws. The physical laws remain premises. |
| Local Proposition I area law | Given curve; [MotionSampling.Conditions and RadialChart](BarrowLib/Polygon/MotionSampling.lean); the displayed area assignment/convention | The conditional local swept-sector law and the stated mechanical approximation controls. General area existence and unrestricted historical scope remain open. |

There are no project `axiom` declarations in the checked mathematical snapshot;
safe proofs use only Lean's standard `propext`, `Classical.choice` and
`Quot.sound`. This is compatible with the explicit mathematical inputs above.
The classical exhaustion specialization is a visible field of the supplied
rules, with its exact Greek source. It is not counted as a proved theorem or
treated as a discharged goal for arbitrary magnitude domains.

## Source versus project authorship

Historical-language witness sections and theorem-level source attributions
are different units. The witness counts below describe the owning files;
they do not certify every theorem in their dependency cascades. A known result
does not become an original result because its Lean proof was written here.
Helpers with no checked exact source remain source-unverified, unless their
own statement and proof are explicitly presented as a project derivation.

| Cascade component | Exact source witnesses | Theorems and provenance boundary |
| --- | ---: | ---: |
| `LemmaII.lean` | 2 edition witness sections (1687, 1713) | 30 formal declarations; 2 nonmonotone exhaustion, 2 nonmonotone multiple-ratio, 2 assigned-area ratio, 4 magnitude and 4 interior-rectangle extensions are explicit editorial reconstructions |
| `LemmaIII.lean` | 2 edition witness sections (1687, 1713) | 22 formal declarations, including 2 separate anachronical results; 2 nonmonotone exhaustion, 2 nonmonotone multiple-ratio, 2 assigned-area ratio, 2 magnitude and 2 interior-rectangle extensions are explicit editorial reconstructions |
| `LemmaIII/CorollaryI.lean` | 2 edition witness sections (1687, 1713) | 14 formal declarations; 2 nonmonotone exhaustion, 2 nonmonotone free-staircase, 2 matched-family, 2 magnitude and 2 monotone staircase clients are explicit editorial coordinate reconstructions |
| `ClassicsLib` | 6 source-linked result files; `FiniteLattice` is support | 26 formal declarations; determinant interpretations, Aristotle's proof reconstruction and the qualified Nine Chapters domains are explicit in their files |
| Unreviewed `BarrowLib` support | Euclid I.41 is background for supplied area rules | 910 declarations remain U in the current bounded census; exact sourced/authored split is not inferred from the library name |
| Zero-base/tail-ratio support since `1a20c9d` | 0 exact external result claims | 9 explicit project derivations, 5 public and 4 private; no historical priority claims |
| Explicit staircase support | 0 exact external result claims | 6 public project derivations: two node inclusions, two endpoint-box inclusions and two actual rectangle-union inclusions |
| Assigned-magnitude support | Euclid X.1 exact-halves clause supports one supplied premise; V.4–5 are context | 3 shared project theorems and 8 edition-local extensions; the source premise is not added to the sourced-theorem count |
| Assigned-area unit-ratio support | Euclid V.2/V.5 supply comparison language, not this limit theorem | 6 shared project theorems, including 2 private, and 4 edition-local clients; all are internally derived formulations, without priority claims |
| Nonmonotone rectangular-exhaustion support | 0 exact external result claims; X.1 halving remains a separately sourced premise | 7 new shared graph theorems (4 private), 1 extracted finite comparison and 6 edition-local clients, all explicit project derivations |
| Nonmonotone free-staircase support | 0 exact external result claims | 4 shared project proofs, including 1 private height-distance proof, and 2 edition clients; no area assignment or enclosure premise is used |
| Matched-family support | 0 exact external result claims | 1 shared project proof and 2 edition clients align the mesh/height quantifiers and derive simultaneous enclosure, area and boundary approximation |
| `ModernLib` | No exact original-language result is established by this aggregate row | 1157 formal declarations; exact sourced/authored split remains unverified |

The two Lemma II and two Lemma III witness sections preserve their separate
Latin passages and edition-local proof interfaces. Their theorem declarations
are formalizations written here; the source passage does not certify every
supporting coordinate lemma. The earlier positive-cell and tail-positivity
results are retained. The new `rectangle_interior_denominator_bound` constructs
an explicit uniform bound from the area of the fixed rectangle `[c,b]×[0,g(c)]`.
Containment in every upper cover and exhaustion of the upper/lower gap bound
both sums eventually by half that rectangle's area. The repaired
`varying_ratios_approach_one_eventually` returns a real offset and reuses the
existing mutual-ratio proof, avoiding the previous vacuous index implication.
`rectangle_mutual_ratios_interior` composes these facts; four edition-local
clients use their own exhaustion proofs and two edition-local reductions.
The original English statements and checked derivations are their provenance;
the Newton passages support the proof route, not a quotation of this coordinate
extension. Anonymous harness examples do not count as project theorems.

The original monotone staircase construction uses the same ordered nodes and left/right heights
as the actual rectangle unions. Horizontal tops and vertical joins are explicit
coordinate sets. The lower construction omits the last rise to the final curve
ordinate, which would exceed the last lower rectangle. The upper construction
includes the initial partial side. Both trace-to-union inclusions are proved;
neither is supplied in a premise. Each historical client uses its own
rectangle-cover estimate and the shared node approximation to derive two-sided
approach. Fixed baseline and remaining endpoint sides, general area existence
and arclength are outside that conclusion. The exact English statements and
checked proofs provide the new coordinate results' project provenance.

The proof-tree number counts the total actually used project cascade,
including library theorems. The import-tree number counts the total available
cascade, including unused theorems. Neither predicts how many further lemmas
will be needed to complete the historical result. The provenance breakdown
above counts the inspected declarations inside each actual proof tree and
retains the remainder as unverified.

For a numerical sourced-versus-internally-derived count, the recent additions
form a completely inspected, disjoint slice:

| Declaration slice | Exact external statement matches asserted | Explicit project derivations | Unclassified in this slice |
| --- | ---: | ---: | ---: |
| New Lemma II interior reductions and clients | 0 | 4 | 0 |
| New Lemma III interior clients | 0 | 2 | 0 |
| BarrowLib zero-base/tail support since `1a20c9d` | 0 | 9 | 0 |
| BarrowLib staircase support | 0 | 6 | 0 |
| New Corollary I staircase clients | 0 | 2 | 0 |
| New magnitude support and edition clients | 0 | 11 | 0 |
| New integer-multiple ratio support and clients | 0 | 10 | 0 |
| New nonmonotone rectangle support and clients | 0 | 14 | 0 |
| New nonmonotone free-staircase support and clients | 0 | 6 | 0 |
| New matched-family support and clients | 0 | 3 | 0 |
| Total of these additions | 0 | 67 | 0 |

“Project derivation” identifies the provenance of the exact statement and
proof, not mathematical novelty. These 67 declarations are not 67 historical
lemmas, and not all are used by every client. Older declarations and their
transitive source attributions are outside this inspected slice. Future
cascade censuses must deduplicate actual compiled dependencies and retain an
unclassified count rather than assigning unsourced known mathematics to the
project. Exact source matches and project derivations must use the same
theorem-level unit; witness-section counts cannot supply that split.

## Which declarations received a provenance classification

The following review is deliberately bounded. The local Lean statements,
their proofs and their opening source/proof-correspondence comments were
inspected. Source matching here concerns the statements recorded in those
files; this increment performs no new manuscript or scan collation. The
external witness URLs and original-language passages remain at those
locations.

| Reviewed group | S | R | P | Reason and locator |
| --- | ---: | ---: | ---: | --- |
| [Euclid IX.20](ClassicsLib/Euclid/PropositionIX20.lean), own declarations | 1 | 2 | 2 | `infinitude_primes` represents the finite-collection statement. `prime_outside_positive_list` and `exists_prime_ge` are explicit reformulations; `finiteProduct_positive` and `divides_finiteProduct` are the exposed arithmetic helpers. The proof substitutes a common product for Euclid's least common multiple. Euclid retains the mathematical attribution. |
| [Euclid VII.31](ClassicsLib/Euclid/PropositionVII31.lean) | 0 | 1 | 0 | `prime_divisor` extends the quoted composite-number statement to every natural number greater than one, including primes. That difference is why it is R. |
| [Euclid I.37](ClassicsLib/Euclid/PropositionI37.lean) and [I.38](ClassicsLib/Euclid/PropositionI38.lean) | 0 | 2 | 0 | `parallel_identity` and `extension_identity` are determinant special cases, without full synthetic area semantics. |
| [Aristotle comparison](ClassicsLib/Aristotle/SquareRootTwo.lean) | 0 | 2 | 2 | `no_natural_ratio_square_two` and `no_integer_ratio_square_two` reconstruct the attested parity contradiction. `even_of_even_square` and `halve_square_equation` expose the arithmetic steps; the exact descent is not attributed to Aristotle. |
| [Finite lattice controls](ClassicsLib/Euclid/FiniteLattice.lean) | 0 | 0 | 4 | The four named orientation, degeneracy and repeated-coverage controls are concrete statements checked here; anonymous examples are excluded. |
| [Lemma I](NewtonLimitDynamics/Historical/LemmaI.lean) | 0 | 7 | 0 | Six printed-edition ordered-exhaustion/terminal-zero formulations and one separately qualified NATP00090 enclosing-ratio reconstruction. Explicit interfaces qualify the source correspondence. |
| [Lemma II](NewtonLimitDynamics/Historical/LemmaII.lean) | 0 | 16 | 14 | Eight source-related rational formulations per printed edition; two interior-rectangle, two assigned-magnitude, one assigned-area ratio, one nonmonotone exhaustion and one nonmonotone multiple-ratio extension per edition are P. |
| [Lemma III](NewtonLimitDynamics/Historical/LemmaIII.lean) | 0 | 10 | 10 | Five source-related unequal-width reconstructions, one interior, one assigned-magnitude, one assigned-area ratio, one nonmonotone exhaustion and one nonmonotone multiple-ratio extension per edition. The two anachronical completed-enclosure theorems remain U in this source census. |
| [Lemma III Corollary I](NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean) | 0 | 4 | 10 | Area and rectangle-cover reconstructions in each edition are R; two monotone staircase-edge, two assigned-magnitude, two nonmonotone exhaustion, two nonmonotone free-staircase and two matched-family clients are P. |
| [MonotoneRectangles](BarrowLib/Polygon/MonotoneRectangles.lean), selected additions | 0 | 0 | 6 | `exists_positive_width_from_aux`, `exists_positive_width_from`, `interval_left_gap_le_total`, `interval_right_gap_le_total`, `lower_sum_eventually_positive`, `upper_sum_eventually_positive`; the first four are private. |
| [RectangleContent](BarrowLib/Polygon/RectangleContent.lean), selected additions | 0 | 0 | 3 | `varying_ratios_approach_one_eventually`, `rectangle_interior_denominator_bound`, `rectangle_mutual_ratios_interior`. |
| [RationalBoundary](BarrowLib/Polygon/RationalBoundary.lean), selected additions | 0 | 0 | 7 | The lower/upper pairs `nodes_in_*_staircase`, `*_staircase_in_rectangles` and `*_staircase_in_figure`; `perturbed_trace_approaches` derives the two-sided approximation under vanishing node errors. |
| [MagnitudeContent](BarrowLib/Polygon/MagnitudeContent.lean) | 0 | 0 | 12 | `enclosure_errors_lt`, `curved_area_enclosure`, `rational_exhaustion`, `errors_vanish`, `multiple_monotone`, `multiple_embed`, `ratios_one_of_enclosure`, `rectangle_magnitude_ratios`, `finite_ratios_of_enclosure`, `rationalMultiples` and private `scale_succ`/`scale_gap_compare`. The existing rational compatibility proof is now declared as a theorem. X.1 and the general compatibility laws remain supplied fields. |
| [UniformRectangles](BarrowLib/Polygon/UniformRectangles.lean) | 0 | 0 | 13 | `rectangle_enclosure`, `fine_rectangles`, `exhaustion`, `positive_rectangle`, `ratios_exhaustion`, `staircase_in_strips`, `staircase_approaches`, `matched_approximation`; private `lower_properties`, `height_enclosure`, `height_distances`, `height_gap`, `value_gap_bound`. Exact English statements and proofs identify project derivations; uniform continuity is not a quoted Newton hypothesis. |
| Distinct reviewed declarations | 1 | 44 | 83 | 128 theorem declarations; these owning groups are disjoint. |

These classifications were intersected with the actual compiled dependency
closures to obtain the per-cascade table. Shared dependencies were counted
once; private names were resolved to their source declarations. Each
partition was checked against the existing compiled proof-tree total. The
README count checker verifies the totals automatically; the source
classifications in this Markdown report are a bounded manual review.

The reviewed derivations are not added to every cascade. The P columns above
count their actual intersections, including reviewed encoding helpers.
`AreaLaw` has 23 P dependencies from that larger reviewed set; the new
nonmonotone ratio clients add none to its proof tree, which remains 880.
Older internally derived support can remain among its 851 U entries.

When the mathematical snapshot changes, refresh the compiled totals and
their intersections with these reviewed groups. Classify further results
only after checking their exact source or their explicit project derivation;
leave the remaining nodes U. This keeps provenance coverage separate from
the README's estimates of remaining proof work.

The new classical premise is the unit-halving specialization of
[Euclid X.1](docs/classics/euclid-X1.md). It is supplied explicitly in the
area-magnitude rules and verified in their rational realization, with no
new Lean `axiom` declaration. The pullback and its eleven original extensions,
and the ten integer-multiple ratio additions, remain project derivations.
[V.2, 4 and 5](docs/classics/euclid-V.md) delimit multiples, comparability and
ratio language; they supply no sequence-limit or general area-existence premise.

The nonmonotone construction uses `max(0,H-eps)` and `H+eps` at each left
sample. Uniform continuity bounds all intervening ordinates, so no endpoint
monotonicity, attained extremum or finite monotone decomposition is assumed.
The finite strips have actual area assignments from existing cut rules, and
their summed gap is bounded by `2*eps*(b-a)`. X.1 halving and rational scaling
select eps and delta for each magnitude tolerance; the extracted
`enclosure_errors_lt` proves both errors from the finite gap. This argument
extends the printed figure scope but does not reproduce Newton's endpoint
telescoping proof. Its edition-local clients use Lemma II → III → Corollary I
within each edition, without inventing a Lemma I dependency for this route.
The original monotone ratio/staircase results and all exact Latin remain.
The subsequent nonmonotone ratio extension constructs a positive rectangle
from a positive ordinate and continuity. Its area R lies below the assigned
area and upper rectangle area. A sufficiently small finite gap derives
R/2 as a lower bracket, then the shared finite multiple comparison gives
all three lower/upper/assigned-area comparisons. Each fixed positive n<m
has a positive height cutoff; every smaller positive height tolerance has
a positive mesh threshold admitting every finer partition. This is a
conditional two-tolerance result, not exact finite ratio equality or a
mesh-only limit at arbitrary fixed height tolerance. Two shared geometric
proofs, one extracted finite comparison, four edition clients and the
def-to-theorem conversion add eight named declarations (all P); the last
conversion adds no mathematics. No area-existence or ratio-limit premise
is added, and no external textual match or priority is claimed.

The separate nonmonotone free-boundary extension uses the same clipped
left-sample heights as that area construction. Vanishing node perturbations
and mesh give two-sided approach; falling and rising internal joins lie in
the higher adjacent rectangle. Both traces use the lower staircase's
internal-join convention, even for the upper height formula; neither adds
a terminal rise. Four shared proofs and two edition clients are P, with
their exact statements and checked derivations as provenance. No area
assignment is used. Independent mesh/error shrinkage proves boundary
approximation, while graph enclosure additionally requires the coupled
fine-mesh condition. Fixed sides and full topological perimeter remain open.

The matched-family theorem now derives that coupling rather than supplying
it. For each positive `eps m`, continuity gives a fine-mesh cutoff; the
vanishing original mesh reaches it. Recursive maxima choose strictly
increasing indices at least m and past that cutoff. Thus the selected mesh
still vanishes, and the finite gap bound tends to zero with eps. The existing
X.1 transfer and finite comparison give assigned-area errors on this same
family, while the staircase theorem gives both free-edge limits. This
re-pairs selected partitions with `eps m`, rather than selecting the original
partition–tolerance pairs together. `Classical.choose` proves existential
selection, not an executable modulus. One shared proof and two edition
clients are P; area existence and fixed-side scope remain explicit gaps.

Historical relocation of fraction arithmetic is separate from this census.
The user's proposed Euclid VII.19 and Nine Chapters authorities still need
exact passages and operation-level correspondence; see
[the boundary note](research/BARROWLIB_BOUNDARY.md). The independent Nine
Chapters attestation below now supplies its bounded Chinese rules. The Greek
criterion and additional signed operations remain an open source audit.
Moving an unchanged representation changes ownership, not the total theorem
count, and earns no completion credit.

## Nine Chapters attestation, independently available

[FractionRules.lean](ClassicsLib/NineChapters/FractionRules.lean) imports no
project module and is imported only by the ClassicsLib entry point. No
existing historical proof is routed through it. Its ten declarations form
an independent proof tree, so adding them changes the ClassicsLib aggregate
and loaded-project total, with no increase in Newton's proof dependencies.
Core Rat/Nat/List lemmas remain excluded from project M/H and cascade counts.

| Theorem in `ClassicsLib.NineChapters` | Kind | Source and qualification |
| --- | --- | --- |
| `commonMeasure_eq_gcd` | R | 約分術: the positive subtraction algorithm's 等數 is identified with Nat.gcd; optional preliminary halving is separate. |
| `yuefen_value` | S | 約分術: division by the common measure preserves a positive fraction; simultaneous halving is also verified. |
| `hefen` | S | 合分術: two positive fractions give the sum of cross-products over the product denominator. |
| `jianfen` | S | 減分術: strictly smaller is subtracted from larger, with positive inputs and positive remainder. |
| `kefen` | R | 課分術: the text computes the excess; the theorem isolates its cross-product comparison criterion as an iff. |
| `pingfen` | R | 平分術: a nonempty positive list conserves its total and redistributes to the mean; the common-denominator work array is abstracted. |
| `chengfen` | S | 乘分術: positive numerators and denominators multiply separately. |
| `jingfen` | S | 經分術: positive money/people quantities, possibly fractional, give the reciprocal-product share. |
| `zhengfu_sub` | R | 正負術 subtraction clause: named positive whole magnitudes and absent entries embedded in Rat; cases determine the surviving name. |
| `zhengfu_add` | R | 正負術 addition clause: the same qualified sign/magnitude encoding. |

Exact Chinese rules and proof correspondence are beside each theorem.
[Chapter I](docs/classics/nine-chapters-I.md) and
[chapter VIII](docs/classics/nine-chapters-VIII.md) retain the witness, fixed
page revision, archived rendered HTML and SHA-256. The latter separately
quotes Liu Hui's naming commentary, conventionally dated 263. The source
review does not attest signed multiplication, general zero arithmetic or
signed order. Source-only/alternate witnesses can be preserved for future
verification without adding proof dependencies. This attestation earns no
completion credit and does not imply that Newton used these texts.
