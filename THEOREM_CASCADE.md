# Theorem cascade and provenance

This note records the detailed meaning of the theorem counts in the README.
The counts are produced from the compiled Lean environment by
`research/CheckReferences.lean`; they are not a count of historical
propositions and they are not additive across rows.

The mathematical snapshot is `a116c87` (9 October 2026). This report's
provenance review changes no theorem or completion estimate. The README
keeps the progress estimates and compact measurements; this file explains
the kinds of result, their sources and the provenance coverage of the
dependencies actually used.

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

The current compiled cascade (9 October, explicit staircase-edge increment) is:

| Entry | Own | Proof tree | Import tree |
| --- | ---: | ---: | ---: |
| `AreaLaw.lean` | 73 | 884 | 1777 |
| `CompositionOfMotions.lean` | 13 | 48 | 169 |
| `LawI.lean` | 0 | 0 | 97 |
| `LawII.lean` | 0 | 0 | 83 |
| `LawsCorollaryV.lean` | 4 | 45 | 124 |
| `LawsCorollaryVI.lean` | 4 | 33 | 124 |
| `LemmaI.lean` | 7 | 18 | 78 |
| `LemmaII.lean` | 20 | 105 | 303 |
| `LemmaIII.lean` | 14 | 149 | 427 |
| `LemmaIII/CorollaryI.lean` | 6 | 98 | 473 |
| `LemmaIII/CorollaryII.lean` | 2 | 70 | 475 |
| `LemmaIII/CorollaryIII.lean` | 10 | 208 | 609 |
| `LemmaIII/CorollaryIV.lean` | 12 | 469 | 1354 |
| `LemmaX.lean` | 4 | 14 | 67 |
| `LemmaX/CorollaryI.lean` | 2 | 14 | 77 |
| `LemmaX/CorollaryII.lean` | 4 | 24 | 79 |
| `LemmaX/CorollaryIII.lean` | 1 | 20 | 80 |
| `LemmaX/CorollaryIV.lean` | 2 | 23 | 82 |
| `LemmaX/CorollaryV.lean` | 2 | 23 | 82 |
| `PropositionII.lean` | 0 | 0 | 28 |
| `PropositionIII.lean` | 0 | 0 | 45 |
| `PropositionIV.lean` | 0 | 0 | 64 |
| `ClassicsLib` | 16 | 16 | 26 |
| `BarrowLib` | 983 | 983 | 983 |
| `ModernLib` | 1157 | 1496 | 1689 |

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
| `AreaLaw.lean` | 0 | 6 | 0 | 878 | 884 |
| `CompositionOfMotions.lean` | 0 | 0 | 0 | 48 | 48 |
| `LawI.lean` | 0 | 0 | 0 | 0 | 0 |
| `LawII.lean` | 0 | 0 | 0 | 0 | 0 |
| `LawsCorollaryV.lean` | 0 | 0 | 0 | 45 | 45 |
| `LawsCorollaryVI.lean` | 0 | 0 | 0 | 33 | 33 |
| `LemmaI.lean` | 0 | 7 | 0 | 11 | 18 |
| `LemmaII.lean` | 0 | 20 | 7 | 78 | 105 |
| `LemmaIII.lean` | 0 | 18 | 7 | 124 | 149 |
| `LemmaIII/CorollaryI.lean` | 0 | 10 | 8 | 80 | 98 |
| `LemmaIII/CorollaryII.lean` | 0 | 2 | 0 | 68 | 70 |
| `LemmaIII/CorollaryIII.lean` | 0 | 10 | 0 | 198 | 208 |
| `LemmaIII/CorollaryIV.lean` | 0 | 2 | 0 | 467 | 469 |
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
| `ClassicsLib` | 1 | 7 | 8 | 0 | 16 |
| `BarrowLib` | 0 | 0 | 15 | 968 | 983 |
| `ModernLib` | 0 | 2 | 0 | 1494 | 1496 |

Across the whole loaded project environment, deduplicating rather than
adding these overlapping rows, this bounded review classifies **76 of 2336
theorems: 1 S, 44 R and 31 P; 2260 remain U**. This measures provenance-review
coverage, not proof completeness, novelty or a library's historical class.
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
| [LemmaII](NewtonLimitDynamics/Historical/LemmaII.lean) | Equal-width finite rectangle areas, gap exhaustion and mutual ratios, including positive-interior zero-base patches on a tail. Assigned curved-area statements retain that premise. | 2: 1687, 1713 |
| [LemmaIII](NewtonLimitDynamics/Historical/LemmaIII.lean) | Unequal-width counterparts using the same edition's Lemmas I/II and supplied shrinking mesh; modern completion is separate. | 2: 1687, 1713 |
| [LemmaIII Corollary I](NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean) | Assigned-area error decay and two-sided approximation of explicit free staircase tops/vertical joins under continuity/mesh premises. The traces lie in their actual rectangle unions; fixed sides are omitted. | 2: 1687, 1713 |
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
has 57 primary and 16 anachronical, `LemmaIII` has 12 and 2, and its
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
| Boundary corollaries | [UniformOn](BarrowLib/Polygon/RationalBoundary.lean), shrinking mesh, and supporting/contact data where needed | Two-sided approximation of the stated traces. Tangent existence and arclength are not inferred. |
| Motion composition and laws' corollaries | [InertialMotion](NewtonLimitDynamics/Historical/LawI.lean), [AdditiveImpulse / CalibratedChange](NewtonLimitDynamics/Historical/LawII.lean), shared time and the displayed update rules | Endpoint geometry and finite motion consequences under those laws. The physical laws remain premises. |
| Local Proposition I area law | Given curve; [MotionSampling.Conditions and RadialChart](BarrowLib/Polygon/MotionSampling.lean); the displayed area assignment/convention | The conditional local swept-sector law and the stated mechanical approximation controls. General area existence and unrestricted historical scope remain open. |

There are no project `axiom` declarations in the checked mathematical snapshot;
safe proofs use only Lean's standard `propext`, `Classical.choice` and
`Quot.sound`. This is compatible with the explicit mathematical inputs above.
A future sourced classical axiom or supplied exhaustion rule would need its
own visible premise and exact source, rather than being hidden in a theorem
count or treated as a discharged goal.

## Source versus project authorship

Historical-language witness sections and theorem-level source attributions
are different units. The witness counts below describe the owning files;
they do not certify every theorem in their dependency cascades. A known result
does not become an original result because its Lean proof was written here.
Helpers with no checked exact source remain source-unverified, unless their
own statement and proof are explicitly presented as a project derivation.

| Cascade component | Exact source witnesses | Theorems and provenance boundary |
| --- | ---: | ---: |
| `LemmaII.lean` | 2 edition witness sections (1687, 1713) | 20 formal declarations; 4 interior-rectangle extensions are explicitly editorial reconstructions |
| `LemmaIII.lean` | 2 edition witness sections (1687, 1713) | 14 formal declarations; 2 interior-rectangle extensions are explicitly editorial reconstructions |
| `LemmaIII/CorollaryI.lean` | 2 edition witness sections (1687, 1713) | 6 formal declarations; 2 staircase clients are explicit editorial coordinate reconstructions |
| `ClassicsLib` | 5 source-linked result files; `FiniteLattice` is support | 16 formal declarations; determinant interpretations and Aristotle's proof reconstruction are qualified in their files |
| Prior `BarrowLib` support | Euclid I.41 is background for supplied area rules | 968 prior theorems; exact sourced/authored split has not been verified and is not inferred from the library name |
| Zero-base/tail-ratio support since `1a20c9d` | 0 exact external result claims | 9 explicit project derivations, 5 public and 4 private; no historical priority claims |
| Explicit staircase support | 0 exact external result claims | 6 public project derivations: two node inclusions, two endpoint-box inclusions and two actual rectangle-union inclusions |
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

The staircase construction uses the same ordered nodes and left/right heights
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
| Total of these additions | 0 | 23 | 0 |

“Project derivation” identifies the provenance of the exact statement and
proof, not mathematical novelty. These 23 declarations are not 23 historical
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
| [Lemma II](NewtonLimitDynamics/Historical/LemmaII.lean) | 0 | 16 | 4 | Eight source-related rational formulations per printed edition; the two explicitly editorial interior-rectangle extensions per edition are P. |
| [Lemma III](NewtonLimitDynamics/Historical/LemmaIII.lean) | 0 | 10 | 2 | Five primary unequal-width reconstructions and one interior extension per edition. The two anachronical completed-enclosure theorems remain U in this source census. |
| [Lemma III Corollary I](NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean) | 0 | 4 | 2 | Area and rectangle-cover reconstructions in each edition are R; the two explicit staircase-edge clients are P. |
| [MonotoneRectangles](BarrowLib/Polygon/MonotoneRectangles.lean), selected additions | 0 | 0 | 6 | `exists_positive_width_from_aux`, `exists_positive_width_from`, `interval_left_gap_le_total`, `interval_right_gap_le_total`, `lower_sum_eventually_positive`, `upper_sum_eventually_positive`; the first four are private. |
| [RectangleContent](BarrowLib/Polygon/RectangleContent.lean), selected additions | 0 | 0 | 3 | `varying_ratios_approach_one_eventually`, `rectangle_interior_denominator_bound`, `rectangle_mutual_ratios_interior`. |
| [RationalBoundary](BarrowLib/Polygon/RationalBoundary.lean), selected additions | 0 | 0 | 6 | The lower/upper pairs `nodes_in_*_staircase`, `*_staircase_in_rectangles` and `*_staircase_in_figure`. |
| Distinct reviewed declarations | 1 | 44 | 31 | 76 theorem declarations; these owning groups are disjoint. |

These classifications were intersected with the actual compiled dependency
closures to obtain the per-cascade table. Shared dependencies were counted
once; private names were resolved to their source declarations. Each
partition was checked against the existing compiled proof-tree total. The
README count checker verifies the totals automatically; the source
classifications in this Markdown report are a bounded manual review.

This also explains why the 23 recent project derivations are not added to
every cascade. Seven occur in Lemma II's proof tree, seven in Lemma III's,
and eight in Corollary I's; none occurs in the current `AreaLaw` proof tree.
The latter's P=0 only concerns the 31 inspected project derivations, while
older internally derived support can remain among its 878 U entries.

When the mathematical snapshot changes, refresh the compiled totals and
their intersections with these reviewed groups. Classify further results
only after checking their exact source or their explicit project derivation;
leave the remaining nodes U. This keeps provenance coverage separate from
the README's estimates of remaining proof work.

No new classical or Barrow-era axiom was introduced for this increment. If a
future reduction in theorem proliferation uses an axiom, it must be declared
explicitly, placed in the correct historical library, and accompanied by an
original-language passage stating that exact premise. It must also remain
visible in the compiled dependency and provenance checks; an unattributed
convenience axiom would not count as historical progress.
