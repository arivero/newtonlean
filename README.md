# Newton's changing proof architecture

This repository formalizes Newton's Book I, Section II, Propositions I–IV in
Lean 4.19.0 core/Std, with no mathlib. De Motu antecedents, the 1687 edition
and the 1713 edition keep their own statements, proof passages and premises.
Proposed 1694 and 1726 material serves comparison without supplying earlier
premises silently.

Start with [the goals](research/GOALS.md),
[the current handoff](research/HANDOFF-2026-10-06-REWORKED-SOURCES.md) and
[state and open obligations](research/STATE.md). Proposition I comes first.
The complete historical proofs remain open; finite, conditional and modern
results are labelled by their actual scope. The progress table below gives
estimates of work done relative to total expected work. Separate measurements
record source lines, theorem declarations and theorem dependency graph sizes.
The linked declarations and remaining obligations determine what has been proved.

## Historical files and libraries

[Historical results](NewtonLimitDynamics/Historical/) have one file per theorem,
lemma, law or corollary, with separate witness sections. Each section contains
exact Latin, source path/hash/URL and proof correspondence, with definitions and
checked results where available. Newton Project TEI in docs/m1 and docs/m4 is
the transcription authority; see [source coverage](research/sources.md).

BarrowLib contains elementary arithmetic, finite geometry and explicit
exhaustion arguments. ClassicsLib contains source-identified classical
mathematics, including Euclidean coordinate special cases, infinitude of primes
and the integer-ratio obstruction for √2. ModernLib contains
completion, modern motion constructions and diagnostics. Primary historical
proofs use elementary/classical support and untainted historical results.
Anachronical proofs occupy a section below five full lines of `=` and
`ANACHRONICAL PROOFS`. Modern use taints downstream types and proofs, including
private helpers and uses across files. An import alone does not classify every
declaration in a file.

The trajectory is given explicitly in the primary route, with mechanical laws
and regularity separately stated. Proposition I must prove swept sector areas
proportional to time. Nonnegative area between the curve and Newton's polygon
is separate approximation control. Neither area conclusion nor polygon/curve
agreement is included in existence.

The retained general construction proves local interval fan proportionality
and between-path content decay under regional calibrated conditions. A theorem
for a given trajectory derives the same conclusions under explicit local consistency.
These modern constructions remain separate from the primary historical route,
which now proves a conditional local swept-sector law for a given motion in a
positive monotone rational chart. Extending that result to the full historical
scope remains open. Kepler is a later application of the general Proposition I
proof.

The [Latin proof route](research/PROP_I_REALIZATION.md),
[two-area distinction](research/PROP_I_PATH_DEFECT.md),
[construction](research/CAUCHY_REALIZATION.md) and
[dependency diagrams](research/figures.md) give focused details. Diagrams derive
from current historical source comments and compiled declarations. The separate
[action arguments](research/action-arguments/README.md) supply no historical
premises or assumed universal constant.

Library names specify the admitted mathematical layers. Exact-result
authorities and original-language passages belong in the owning files:

| Library | Authorities and checked scope | Source work remaining |
| --- | --- | --- |
| [ClassicsLib](ClassicsLib.lean) | Euclid's *Elements* [I.37](ClassicsLib/Euclid/PropositionI37.lean), [I.38](ClassicsLib/Euclid/PropositionI38.lean), [VII.31](ClassicsLib/Euclid/PropositionVII31.lean) and [IX.20](ClassicsLib/Euclid/PropositionIX20.lean), plus Aristotle, *Prior Analytics* I.23, 41a26–27 in [SquareRootTwo](ClassicsLib/Aristotle/SquareRootTwo.lean). Original Greek and exact URLs are in the files. | I.37/I.38 remain determinant special cases. IX.20 uses a finite product in place of Euclid's least common multiple. Aristotle attests the parity contradiction, not the full reconstructed descent proof or a constructed geometric diagonal. Full synthetic area semantics and exact-result provenance of the older model's helpers remain separate obligations. |
| [BarrowLib](BarrowLib.lean) | [SectorFan](BarrowLib/Polygon/SectorFan.lean) quotes Greek from Euclid [I.41](https://physics.ntua.gr/mourmouras/euclid/book1/postulate41.html), the triangle/parallelogram area relation, and the [Common Notions](https://physics.ntua.gr/mourmouras/euclid/book1/elements1.html), as background for the supplied area rules. SectorFan, [TriangleContent](BarrowLib/Polygon/TriangleContent.lean), [FanDifference](BarrowLib/Polygon/FanDifference.lean), [BoxCoverArea](BarrowLib/Polygon/BoxCoverArea.lean) and [AreaDomain](BarrowLib/Polygon/AreaDomain.lean) state their own English project derivations without historical textual support or priority claims. | The library name does not attribute its contents to Isaac Barrow. Original-language, exact-result attribution for other borrowed helpers remains unverified; the Greek background does not state the new coordinate results. |
| [ModernLib](ModernLib.lean) | The exact checked constructions are in their Lean files, including [CauchyValues](ModernLib/Foundation/Polygon/CauchyValues.lean), [EndpointCauchyName](ModernLib/Foundation/Polygon/EndpointCauchyName.lean) and the conditional [given-trajectory area result](ModernLib/Polygon/GivenTrajectoryArea.lean). | Exact original-language sources for standard borrowed modern results remain to be supplied and verified. Names such as “Cauchy” alone establish no exact attribution; known results are not credited to their AI formalizer. |

## Proof progress

Completion estimates use **work done / (work done + estimated remaining work)**,
assessed separately for each witness and rounded to avoid false precision.
For example, 80% estimates that the remaining work is about one quarter of the
work already done. The measured lines, theorems and dependency sizes below
describe the work already present; the listed open tasks inform the estimate
of what remains. These measurements have different units and are not added
into one score. The percentages are judgments about remaining effort, rather
than fixed stages assigned to particular kinds of result. They may change
when an attempted proof reveals more work. Rows are not averaged into a
project percentage.

Every commit must update this completion-percentage information, reassessing
the affected files and witnesses and explaining changes to the estimates or
remaining work. An unchanged rounded estimate must be explicitly justified
here. Measured counts must also be refreshed whenever they change.
Current reassessment: the two classical comparison examples below are complete
for their stated finite arithmetic conclusions. All Newton file/witness
estimates remain unchanged, including Lemmas II/III at 70%: the new examples
do not alter their proofs or discharge their remaining area/ratio obligations.
The proof-strategy review changes how we select and assess future increments;
it does not discharge an additional Newton obligation or change those estimates.
The zero-base work now isolates and checks the finite lemma that a positive
width cell with a positive left ordinate makes the lower sum positive. It now
also proves the eventual positive lower-sum index from an interior positive
ordinate and a shrinking maximum-width bound, and the retained harness checks
it on the zero-base square patch. The theorem is still a BarrowLib support
result: the source-local Lemma II/III mutual-ratio clients have not yet been
refactored to consume this new hypothesis, and general area/rational-scope
obligations remain open. The rounded Lemma II/III estimates therefore remain
70%, with that unchanged rounding recorded rather than counted as completed
historical proof.

For laws, completion concerns their representation as supplied mechanical
premises. Law I and calibrated Law II are complete in that stated role;
deriving the physical laws is outside the task. **Lemma I is also 100% for its
stated ordered-difference contradiction argument**, including the before-end
time formulation. A candidate ultimate difference and its terminal comparison
properties are supplied explicitly. Constructing ultimate objects is a
separate task; applying Lemma I requires each client to justify its own gap and
comparisons. The percentage does not claim that construction has been done.

Every existing historical Lean file has a row. The De Motu column lists
**NATP00089 / NATP00090** in that order. A dash means that the file has no
formalization for that witness; it makes no claim that a historical counterpart
does not exist. Exact passages, theorem hypotheses and source classifications
remain in the linked files. Modern supporting results have their own measured
work; they do not discharge the remaining primary historical tasks.

| Historical file | De Motu 89 / 90 | 1687 | 1713 | Work done and estimated remaining tasks |
| --- | --- | --- | --- | --- |
| [LawI.lean](NewtonLimitDynamics/Historical/LawI.lean) | — / 100% | 100% | 100% | Complete representation as witness-local inertia predicates for rational, fixed-body motion. The coordinate interpretation is explicit; the law remains a mechanical premise. |
| [LawII.lean](NewtonLimitDynamics/Historical/LawII.lean) | — / 100% | 100% | 100% | Complete representation as calibrated directed velocity-change predicates. Fixed-body mass and impulse calibration are supplied. A general force-to-motion construction is outside this law-interface task. |
| [CompositionOfMotions.lean](NewtonLimitDynamics/Historical/CompositionOfMotions.lean) | 60% / 80% | 80% | 80% | NATP00089 has a finite model of its hypothesis. NATP00090's Lemma 1 and the printed Laws' Corollary I derive diagonal motion from their own laws; independent directions give the unique endpoint intersection, and direct addition handles degenerate directions. Rational coordinates and post-impulse drift remain explicit model choices. |
| [LawsCorollaryV.lean](NewtonLimitDynamics/Historical/LawsCorollaryV.lean) | — / 20% | 80% | 80% | Printed proofs preserve relative states under uniform translation at every cell boundary, using their own laws. Shared time, additive velocities and relative-state impulse rules remain explicit; continuous collision geometry is open. NATP00090 records Lex 3 without attaching a proof. |
| [LawsCorollaryVI.lean](NewtonLimitDynamics/Historical/LawsCorollaryVI.lean) | — / — | 80% | 80% | Common calibrated velocity changes add a shared motion and preserve mutual states at cell boundaries. Continuous forcing and forces depending on absolute states are outside the checked model. Application in historical Proposition III remains open. |
| [LemmaI.lean](NewtonLimitDynamics/Historical/LemmaI.lean) | — / 40% | 100% | 100% | Printed ordered-difference contradiction complete: exclusion of a positive terminal difference, positive time windows before the endpoint and a rational terminal-zero consequence. Approach and terminal comparisons are explicit premises. NATP00090 has only the enclosing-ratio step inside its Lemma 2; tangent-area geometry and its mechanical premises remain open, without attributing a printed Lemma I dependency. |
| [LemmaII.lean](NewtonLimitDynamics/Historical/LemmaII.lean) | — / — | 70% | 70% | Equal-width gap identity, actual rectangle-union areas, exhaustion and use of the edition's Lemma I. Both mutual ratios of the varying finite areas approach one on a nonzero interval with positive starting ordinate: a base rectangle derives their uniform denominator bound, without assigning a curved area. Fixed assigned-area ratios remain available. Zero-base patches, general curved-area existence and non-rational scope remain open. |
| [LemmaIII.lean](NewtonLimitDynamics/Historical/LemmaIII.lean) | — / — | 70% | 70% | Unequal-width gap exhaustion from shrinking maximum width; the edition's Lemma II reduction gives both varying finite-area ratios on the same positive patches. Assigned curved-area approximation and the Lemma I contradiction remain available. Zero-base patches and general area/magnitude scope remain open; applications must establish their own mesh exhaustion. |
| [LemmaIII/CorollaryI.lean](NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean) | — / — | 60% | 60% | Area-error decay through the edition's Lemma III, plus two-sided approximation by rectangle covers of sampled endpoints under continuity and mesh premises. Full geometric coincidence is open; endpoint covers are not the entire staircase perimeter. |
| [LemmaIII/CorollaryII.lean](NewtonLimitDynamics/Historical/LemmaIII/CorollaryII.lean) | — / — | 80% | 80% | Two-sided rational chord-boundary approximation through Corollary I. Uniform continuity and shrinking mesh remain explicit; the theorem gives no area or arclength conclusion. |
| [LemmaIII/CorollaryIII.lean](NewtonLimitDynamics/Historical/LemmaIII/CorollaryIII.lean) | — / — | 80% | 80% | For concave increasing rational patches, supplied contact and concavity derive supporting cells, continuity, the identity of the tangent trace with the polygon's upper boundary, and finite tangent-polygon areas by dissection. Area errors vanish against a supplied curved area. Tangent existence, arbitrary patches and curved-area existence remain open. |
| [LemmaIII/CorollaryIV.lean](NewtonLimitDynamics/Historical/LemmaIII/CorollaryIV.lean) | — / — | 80% | 80% | The edition's Corollaries II/III give chord and actual tangent-polygon upper-boundary approximation on those patches. General curves and identification with force polygons remain open; boundary approximation supplies no arclength limit. Modern completed-curve results stay below the separator. |
| [LemmaX.lean](NewtonLimitDynamics/Historical/LemmaX.lean) | — / — | 40% | 40% | Conditional ordered squeeze and a rational contact-triangle bridge. Velocity-area identification, contact limits and mechanical enclosure are supplied; the invoked Lemma IX is not independently formalized here. The 1713 theorem reuses the 1687 formal interface, explicitly as a mathematical interface rather than a historical dependency. |
| [LemmaX/CorollaryI.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryI.lean) | — / — | 60% | 60% | Normalized errors at proportional times share one positive ultimate coefficient, using the edition's Lemma X. Equal-force calibration and similarity data remain supplied; the ratio of the two varying errors is not formed. |
| [LemmaX/CorollaryII.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryII.lean) | — / — | 60% | 60% | Errors divided by force and squared time share one positive ultimate calibration. Its force proportionality is a premise rather than a consequence of the current Law II predicate; geometric similarity and the mutual error ratio remain open. |
| [LemmaX/CorollaryIII.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryIII.lean) | — / — | — | 60% | Extends Corollary II's normalization to a supplied described-space function. The underlying Lemma X and force-calibration premises remain. |
| [LemmaX/CorollaryIV.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryIV.lean) | — / — | — | 60% | Exact coefficient algebra and an ultimate force normalization derived from Corollary III. The mechanical space/force relation remains supplied through Lemma X. |
| [LemmaX/CorollaryV.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryV.lean) | — / — | — | 60% | Exact coefficient algebra and the ultimate squared-time normalization derived from Corollary III. Positive calibration/force and the mechanical premises remain explicit. |
| [AreaLaw.lean](NewtonLimitDynamics/Historical/AreaLaw.lean) | 60% / 60% | 60% | 60% | Finite equal-area arguments and, for NATP00090 and both printed editions, a conditional local law for the actual swept sector of a given motion. The full mechanical/curve sector difference has shrinking covers with constructed cover areas; any separately assigned difference areas vanish. Actual difference-area existence, general patch assembly, non-rational scope and arbitrary-time polygon/curve agreement remain open. NATP00089 retains its own finite hypothesis/model scope. |
| [PropositionII.lean](NewtonLimitDynamics/Historical/PropositionII.lean) | — / — | 10% | 10% | Source and proof route recorded; the historical file declares no theorem. ModernLib supplies finite signed-area converse support. The historical continuous-curve/force-direction passage and application of Laws' Corollary V remain open. |
| [PropositionIII.lean](NewtonLimitDynamics/Historical/PropositionIII.lean) | — / — | 10% | 10% | Source and proof route recorded; the historical file declares no theorem. ModernLib supplies finite relative-motion support. The edition's Laws' Corollary VI and Proposition II still need to be applied in a historical continuous argument. |
| [PropositionIV.lean](NewtonLimitDynamics/Historical/PropositionIV.lean) | — / — | 10% | 10% | Source and proof route recorded; the historical file declares no theorem. ModernLib supplies a conditional finite sagitta comparison. Circle/force interpretation and the distinct limiting routes remain open: Lemmas V/XI in 1687; Proposition I's Corollaries II/IV and Lemma VII in 1713. |

Dedicated historical files for **Lemmas IV–IX and XI** are still absent
(**0%** work in dedicated historical files). The elementary quadratic/contact
support does not constitute those source proofs. Proposition I's own corollaries required
by the 1713 Proposition IV route also remain to be formalized separately.
De Motu counterparts of Propositions II–IV remain a source-correspondence
question, rather than receiving the printed proofs by analogy.

The next Lemma II–III increment is the zero-base case: from a positive
interior ordinate, derive an eventual positive lower bound for the full lower
rectangle sums, allowing initial zero denominators. The positive-base patch
case now proves both varying finite-area ratio errors vanish without an
assigned curved area. The separate existence problem for
the actual mechanical/curve difference needs a justified area domain:
[AreaDomain.lean](BarrowLib/Polygon/AreaDomain.lean) proves a relative
countermodel to inferring arbitrary difference assignments from the current
translation-and-cut rules. This leaves the proved shrinking-cover construction
and conditional difference-area decay intact. Full obligations and verification
evidence remain in [STATE.md](research/STATE.md) and
[VERIFICATION.md](research/VERIFICATION.md).

### Classical comparison examples

These examples let readers compare a short library proof with the arithmetic
it delegates. Their source comments pin the inspected mathlib version and
describe the substitutions; mathlib is not imported or installed.

| Result and file | Completion in the stated scope | Inspected mathlib route | Checked classical substitute |
| --- | ---: | --- | --- |
| [Prime divisor, VII.31](ClassicsLib/Euclid/PropositionVII31.lean) | 100% | `minFac_prime` and `minFac_dvd` supply a prime divisor. | Finite descent through proper divisors, with the prime criterion explicit. |
| [Infinitude of primes, IX.20](ClassicsLib/Euclid/PropositionIX20.lean) | 100% | `Nat.exists_infinite_primes` uses a prime factor of `n!+1`; its arithmetic argument is already classical. | Multiply a finite positive list, add one, apply VII.31 and exclude every old entry. The numeric `n ≤ p` form is also proved. |
| [√2 integer-ratio obstruction](ClassicsLib/Aristotle/SquareRootTwo.lean) | 100% | `irrational_sqrt_two` passes through prime-square and rational-square criteria and the real square-root interface. | Even square implies even side; a hypothetical ratio gives a smaller positive denominator. Both signs and unreduced integer ratios are covered. |

Here 100% concerns these arithmetic statements. A completed real square root
or synthetic geometric diagonal is outside that scope. In the inspected
mathlib implementation, `Real.sqrt` uses the inverse of a power order
isomorphism on nonnegative reals. Replacing that interface with the explicit
ratio equation removes it entirely from the classical proof. The source review
follows named definitions and proof steps; it is not a compiled transitive
dependency census of mathlib. Our new proofs' compiled dependencies are checked.

The smaller examples also motivate the [proof strategy](research/PROOF_STRATEGY.md).
Their arithmetic foundation is already in Lean core and excluded from our
project counts; Newton's fraction, geometry and approximation foundations are
included. That explains part of the difference. New layers and conditional
wrappers still need justification by the historical obligation they discharge.
The strategy guide reviews public Lean skills and the adaptations required by
our source-first, core-only method.

### Measured work

The measurements cover all witness sections and both primary and anachronical
proofs in each file. Completion above is estimated separately for each witness.

- **Lines**: physical source lines, including Latin, comments and blanks.
- **Own theorems**: named source-declared theorems, including private theorems.
  Definitions, anonymous examples and generated equation lemmas do not count.
- **Proof tree**: distinct project theorems in the file and its actual transitive
  dependencies. Traversal starts from all declarations in the file and follows
  types, definitions, proofs and private helpers. Shared nodes count once.
- **Import tree**: distinct project theorems in the file and all its compiled
  transitive imports, including available theorems that it never uses.

“Tree” therefore counts nodes of a dependency graph, without duplicating shared
branches. Lean/Std infrastructure is excluded. Library rows aggregate their own
source modules and entry point; their dependency counts deduplicate across the
whole library. Counts from different rows overlap and should not be summed.

The measured cascade and its provenance audit are maintained in
[THEOREM_CASCADE.md](THEOREM_CASCADE.md). It explains how own declarations,
actual proof trees and full import trees differ, and records which entries have
an exact source witness versus which are project-authored support. The import
tree is the total theorem cascade, including library theorems.

| File or library | Lines | Own theorems | Proof tree | Import tree |
| --- | ---: | ---: | ---: | ---: |
| [AreaLaw.lean](NewtonLimitDynamics/Historical/AreaLaw.lean) | 2046 | 73 | 884 | 1767 |
| [CompositionOfMotions.lean](NewtonLimitDynamics/Historical/CompositionOfMotions.lean) | 233 | 13 | 48 | 169 |
| [LawI.lean](NewtonLimitDynamics/Historical/LawI.lean) | 70 | 0 | 0 | 97 |
| [LawII.lean](NewtonLimitDynamics/Historical/LawII.lean) | 76 | 0 | 0 | 83 |
| [LawsCorollaryV.lean](NewtonLimitDynamics/Historical/LawsCorollaryV.lean) | 142 | 4 | 45 | 124 |
| [LawsCorollaryVI.lean](NewtonLimitDynamics/Historical/LawsCorollaryVI.lean) | 118 | 4 | 33 | 124 |
| [LemmaI.lean](NewtonLimitDynamics/Historical/LemmaI.lean) | 144 | 7 | 18 | 78 |
| [LemmaII.lean](NewtonLimitDynamics/Historical/LemmaII.lean) | 305 | 16 | 95 | 295 |
| [LemmaIII.lean](NewtonLimitDynamics/Historical/LemmaIII.lean) | 278 | 12 | 140 | 417 |
| [LemmaIII/CorollaryI.lean](NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean) | 97 | 4 | 80 | 455 |
| [LemmaIII/CorollaryII.lean](NewtonLimitDynamics/Historical/LemmaIII/CorollaryII.lean) | 75 | 2 | 70 | 457 |
| [LemmaIII/CorollaryIII.lean](NewtonLimitDynamics/Historical/LemmaIII/CorollaryIII.lean) | 244 | 10 | 208 | 591 |
| [LemmaIII/CorollaryIV.lean](NewtonLimitDynamics/Historical/LemmaIII/CorollaryIV.lean) | 240 | 12 | 469 | 1336 |
| [LemmaX.lean](NewtonLimitDynamics/Historical/LemmaX.lean) | 100 | 4 | 14 | 67 |
| [LemmaX/CorollaryI.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryI.lean) | 70 | 2 | 14 | 77 |
| [LemmaX/CorollaryII.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryII.lean) | 95 | 4 | 24 | 79 |
| [LemmaX/CorollaryIII.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryIII.lean) | 33 | 1 | 20 | 80 |
| [LemmaX/CorollaryIV.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryIV.lean) | 56 | 2 | 23 | 82 |
| [LemmaX/CorollaryV.lean](NewtonLimitDynamics/Historical/LemmaX/CorollaryV.lean) | 58 | 2 | 23 | 82 |
| [PropositionII.lean](NewtonLimitDynamics/Historical/PropositionII.lean) | 55 | 0 | 0 | 28 |
| [PropositionIII.lean](NewtonLimitDynamics/Historical/PropositionIII.lean) | 47 | 0 | 0 | 45 |
| [PropositionIV.lean](NewtonLimitDynamics/Historical/PropositionIV.lean) | 48 | 0 | 0 | 64 |
| [ClassicsLib/Aristotle/SquareRootTwo.lean](ClassicsLib/Aristotle/SquareRootTwo.lean) | 86 | 4 | 4 | 4 |
| [ClassicsLib/Euclid/FiniteLattice.lean](ClassicsLib/Euclid/FiniteLattice.lean) | 43 | 4 | 6 | 16 |
| [ClassicsLib/Euclid/PropositionI37.lean](ClassicsLib/Euclid/PropositionI37.lean) | 23 | 1 | 1 | 1 |
| [ClassicsLib/Euclid/PropositionI38.lean](ClassicsLib/Euclid/PropositionI38.lean) | 25 | 1 | 1 | 1 |
| [ClassicsLib/Euclid/PropositionIX20.lean](ClassicsLib/Euclid/PropositionIX20.lean) | 87 | 5 | 6 | 6 |
| [ClassicsLib/Euclid/PropositionVII31.lean](ClassicsLib/Euclid/PropositionVII31.lean) | 45 | 1 | 1 | 1 |
| [ClassicsLib](ClassicsLib.lean) | 340 | 16 | 16 | 26 |
| [BarrowLib](BarrowLib.lean) | 14746 | 973 | 973 | 973 |
| [ModernLib](ModernLib.lean) | 19677 | 1157 | 1496 | 1688 |

After a build, reproduce or check these rows with the existing compiled checker:

```sh
NEWTON_PRINT_THEOREM_COUNTS=1 lake env lean research/CheckReferences.lean
NEWTON_CHECK_README_COUNTS=1 lake env lean research/CheckReferences.lean
```

## Reverse programme

[Reverse/](Reverse/README.md) runs the opposite direction: a quantum
Kaluza–Klein parent is reduced through named interfaces (KK reduction, weak
decoupling, colour scale, mass gap, confinement, neutral matter,
nonrelativistic and semiclassical limits) to the same Law I / Law II shapes
the historical files consume. It is modern, imports nothing historical and
is imported by nothing historical; `lake build Reverse` builds it.

## Verification

```sh
lake build
lake build Reverse
lake build BarrowLib
lake build ClassicsLib
lake build ModernLib
lake build NewtonLimitDynamics
lake env lean research/CheckReferences.lean
lake env lean scripts/inspect_graphs.lean
sha256sum -c docs/SHA256SUMS
git diff HEAD --check
```

Run the retained Lean scope harnesses described in [verification](research/VERIFICATION.md).
Passing checks certify the stated Lean results without discharging supplied
historical premises. Git retains previous tools, figures and session records;
there are no JSON catalogs, Python bookkeeping scripts or completion plots.

Readable source-specific notes remain in Markdown. Render them on demand:

```sh
pandoc docs/reference/principia-1687-modern.md -o /tmp/principia-1687-modern.pdf \
  --pdf-engine=xelatex -V mainfont='DejaVu Serif' \
  -V monofont='DejaVu Sans Mono' -V mathfont='DejaVu Math TeX Gyre' \
  --toc --toc-depth=2
```

The reader renderings are aids; original sources and historical Lean witness
sections remain authoritative. The [theorem-growth analysis](research/THEOREM_PROLIFERATION.md)
explains why infrastructure and interface counts do not measure discharged
proof obligations.

## Related work and historical proof ordering

Several formalization projects attend to historical sources, proof order and
provenance. [LeanEuclid][leaneuclid] (Murphy et al., ICML 2024) implements in
Lean a variant of System E, which Avigad, Dean and Mumma designed as a faithful
model of the proofs in Euclid's *Elements*, diagrammatic reasoning included.
Its Book I proofs are written to follow Euclid's own arguments closely, with
SMT solvers carrying out the diagrammatic inferences implicitly. Its target is
Euclid's proof practice as well as his theorems.

The closest methodological precedent is
[*Does the Proof Prove It That Way?*][pistis] (Mao et al., 2026). Its Pistis
system formalizes Books I–III of the *Elements* under five necessary
conditions of faithfulness. Formal steps correspond to the source sentences in
their order, and every proposition Euclid cites in a step must already be
available there and applied at that step. A compiling proof of the same theorem
by another route fails these conditions. The method therefore constrains which
earlier propositions and proof steps a formal proof may use.

[Lean of the Mathematical Commons][lmc] is a source-linked Lean 4 library for
classical mathematics, piloted on Emmy Noether's works. It links its entries to
historical source editions, audits Mathlib coverage declaration by declaration
and records formalization gaps. The Mathlib Initiative's
[Formal Frontier][formal-frontier] programme is preparing an autoformalization
specification that will set community standards for how formal code relates
to its informal source and what counts as adequate coverage and faithfulness.
Both concern provenance and source linking; Mathlib itself is organized by
mathematical subject.

newtonlean applies a related idea to Newton's changing proof architecture.
Declarations are separated by historical witness and edition, and a result in
an earlier layer may be repaired only with mathematics and textual assumptions
admitted to that layer. Conceptually, the project treats mathematical knowledge
as a dated filtration

$$\mathcal M_{t_1} \subseteq \mathcal M_{t_2} \subseteq \cdots,$$

in which a historical proof at date or edition $t$ depends only on results and
assumptions admitted into $\mathcal M_t$. A modern dependency DAG records what a
proof uses; the filtration also records whether each use was admissible at $t$.
The library conventions give a coarse version of these layers: ClassicsLib
through Hypatia, BarrowLib after Hypatia and before the Principia, ModernLib
after the Principia. Modern reconstructions remain useful and stay in the marked
anachronical sections, with their taint traced through compiled dependencies.

For Newton the ordering is edition-sensitive as well as chronological, because
he revised the text whose proofs are being formalized. *De Motu*, the 1687
edition, the 1713 edition and later witnesses can differ in statement, premises
and proof architecture. A later edition is therefore evidence for comparison,
not automatically a premise of an earlier proof. The novelty claimed here is
correspondingly narrow: source- and edition-sensitive formalization of
Newton's proof architecture; explicit separation of historical and anachronical
proof resources; treatment of the dependency graph itself as an object of
historical investigation; and, as the work proceeds, a visible record of where
physical assumptions such as Galilean kinematics, or particular limiting
choices, enter a proof.

### References

- Jeremy Avigad, Edward Dean and John Mumma, “A formal system for Euclid's
  *Elements*”, *Review of Symbolic Logic* 2(4), 2009, 700–768,
  [doi:10.1017/S1755020309990098](https://doi.org/10.1017/S1755020309990098),
  [arXiv:0810.4315](https://arxiv.org/abs/0810.4315).
- Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and
  Xujie Si, “Autoformalizing Euclidean Geometry”, ICML 2024,
  [arXiv:2405.17216](https://arxiv.org/abs/2405.17216); code:
  [LeanEuclid][leaneuclid].
- Tadd Mao, Tianjun Zhong, Dhruva Arekar, Yuming Feng, One An, Jiani Huang,
  Xujie Si and Ziyang Li, “Does the Proof Prove It That Way? Faithful
  Formalization of Elements Proofs”, 2026, [arXiv:2608.15432][pistis].
- [Lean of the Mathematical Commons][lmc], Emmy Noether pilot, concept DOI
  [10.5281/zenodo.21129945](https://doi.org/10.5281/zenodo.21129945).
- Mathlib Initiative, [Formal Frontier][formal-frontier].

[leaneuclid]: https://github.com/loganrjmurphy/LeanEuclid
[pistis]: https://arxiv.org/abs/2608.15432
[lmc]: https://github.com/KokunoYumeto/lean-mathematical-commons
[formal-frontier]: https://mathlib-initiative.org/formal-frontier/
