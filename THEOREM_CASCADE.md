# Theorem cascade and provenance

This note records the detailed meaning of the theorem counts in the README.
The counts are produced from the compiled Lean environment by
`research/CheckReferences.lean`; they are not a count of historical
propositions and they are not additive across rows.

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

The current compiled cascade (9 October, interior-rectangle ratio increment) is:

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
| `LemmaIII/CorollaryI.lean` | 4 | 80 | 465 |
| `LemmaIII/CorollaryII.lean` | 2 | 70 | 467 |
| `LemmaIII/CorollaryIII.lean` | 10 | 208 | 601 |
| `LemmaIII/CorollaryIV.lean` | 12 | 469 | 1346 |
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
| `BarrowLib` | 977 | 977 | 977 |
| `ModernLib` | 1157 | 1496 | 1689 |

The README additionally lists line counts and the individual classical files.
Reproduce the compiled measurements and check the README with:

```sh
NEWTON_PRINT_THEOREM_COUNTS=1 lake env lean research/CheckReferences.lean
NEWTON_CHECK_README_COUNTS=1 lake env lean research/CheckReferences.lean
```

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
| [LemmaIII Corollary I](NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean) | Assigned-area error decay and two-sided rectangle endpoint-cover approximation under continuity/mesh premises; full staircase geometry remains open. | 2: 1687, 1713 |
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
| `ClassicsLib` | 5 source-linked result files; `FiniteLattice` is support | 16 formal declarations; determinant interpretations and Aristotle's proof reconstruction are qualified in their files |
| Prior `BarrowLib` support | Euclid I.41 is background for supplied area rules | 968 prior theorems; exact sourced/authored split has not been verified and is not inferred from the library name |
| Zero-base/tail-ratio support since `1a20c9d` | 0 exact external result claims | 9 explicit project derivations, 5 public and 4 private; no historical priority claims |
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

The proof-tree number counts the total actually used project cascade,
including library theorems. The import-tree number counts the total available
cascade, including unused theorems. Neither predicts how many further lemmas
will be needed to complete the historical result. A full sourced-versus-authored
count for each transitive cascade remains unverified; the table above reports
the source coverage actually inspected rather than inventing that split.

For a numerical sourced-versus-internally-derived count, the recent additions
form a completely inspected, disjoint slice:

| Declaration slice | Exact external statement matches asserted | Explicit project derivations | Unclassified in this slice |
| --- | ---: | ---: | ---: |
| New Lemma II interior reductions and clients | 0 | 4 | 0 |
| New Lemma III interior clients | 0 | 2 | 0 |
| BarrowLib zero-base/tail support since `1a20c9d` | 0 | 9 | 0 |
| Total of these additions | 0 | 15 | 0 |

“Project derivation” identifies the provenance of the exact statement and
proof, not mathematical novelty. These 15 declarations are not 15 historical
lemmas, and not all are used by every client. Older declarations and their
transitive source attributions are outside this inspected slice. Future
cascade censuses must deduplicate actual compiled dependencies and retain an
unclassified count rather than assigning unsourced known mathematics to the
project. Exact source matches and project derivations must use the same
theorem-level unit; witness-section counts cannot supply that split.

No new classical or Barrow-era axiom was introduced for this increment. If a
future reduction in theorem proliferation uses an axiom, it must be declared
explicitly, placed in the correct historical library, and accompanied by an
original-language passage stating that exact premise. It must also remain
visible in the compiled dependency and provenance checks; an unattributed
convenience axiom would not count as historical progress.
