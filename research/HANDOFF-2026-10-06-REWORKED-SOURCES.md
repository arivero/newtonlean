# Handoff, 6 October 2026: historical proofs in the reworked sources

This is the active work order, at the user's request. The 4 October general-force
handoff is retired as an execution plan; its completed results and outstanding
questions are preserved below and in Git. Do not resume its task letters or
old file paths as an independent queue. Read AGENTS.md and GOALS.md first.

The user released the review hold with “push as it is”; the verified refactor
and source-only cleanup are pushed as `60180f2`. The further consolidation
removes Python/plots, whole-library interleaving and superseded session records.
Only this handoff remains active. Commit verified increments after the current
checks; the cleanup itself adds no historical proof-completion credit.

## Goal and proof boundary

Prove Proposition I, then II, III and IV, separately for De Motu witnesses,
1687 and 1713. Read Newton's proof paragraphs and follow their actual invoked
results. A dependency comment, unused import or theorem with the desired
conclusion inside its premise bundle does not discharge that step.

Take the trajectory as given. Existence supplies a curve parameter; mechanical
laws and needed regularity remain separate explicit premises. Do not postulate
the curve's swept-area law, its agreement with Newton's polygons or vanishing
between-path area. This convention is user-authorized interpretation, not a
quoted Newton axiom.

Keep three quantities distinct:

- **A:** swept sector area proportional to elapsed time: Proposition I's goal.
- **B:** nonnegative area between polygon and given curve: approximation control.
- **Areal product:** position–velocity determinant: a supporting identity.

Unsigned fan sums count multiplicity. Their proportionality is already proved
in a modern model; identification with ordinary geometric swept-sector area
under explicit orientation/overlap conditions remains open. Neither a trace
limit nor an area budget proves an arclength limit.

Primary historical proofs may use BarrowLib, ClassicsLib and untainted
historical results. ModernLib use, including a type in a theorem statement,
makes that proof anachronical. Keep such proofs below the five-line separator;
do not move Cauchy/quotient machinery into elementary support to hide the use.
An explicit abstract curve need not require constructing a modern completion.

## Read these current files

The historical source files contain the exact Latin, witness paths/hashes,
proof correspondence and dependency evidence:

| Work | Current owner | Present boundary |
| --- | --- | --- |
| Proposition I / De Motu Theorem I | NewtonLimitDynamics/Historical/AreaLaw.lean | Printed law-driven finite construction derives equal triangles and local ordinary sector-union area; De Motu finite steps remain separate; historical curved-sector proof open |
| Laws' Corollary I / De Motu composition | NewtonLimitDynamics/Historical/CompositionOfMotions.lean | Printed editions derive diagonal motion from their own supplied inertia/additive-change predicates; separate De Motu finite models |
| Laws I and II | NewtonLimitDynamics/Historical/LawI.lean; LawII.lean | Source-local statements, Law II explanations and explicit calibrated mechanical predicates |
| Lemma I | NewtonLimitDynamics/Historical/LemmaI.lean | Separate ordered contradiction and positive before-end-window proofs; NATP00090 Lemma 2's unnumbered squeeze comparison |
| Lemmas II and III | NewtonLimitDynamics/Historical/LemmaII.lean; LemmaIII.lean | Actual finite union areas under supplied area rules, fixed positive rational-area ratios, actual historical cross-result uses; arbitrary curved areas remain open |
| Lemma III corollaries | NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean through CorollaryIV.lean | Primary rational approximation chain with explicit continuity/mesh/support data; actual tangents and circumscribed area remain open |
| Propositions II–IV | NewtonLimitDynamics/Historical/PropositionII.lean through PropositionIV.lean | Retained finite/conditional reconstructions; historical limiting routes open |

Use the archived TEI in docs/m1 and docs/m4 as the transcription authority.
The five removed generated research reports/indexes are not live sources.
sources.md retains archive provenance; SHA256SUMS checks retained originals.
The [realization note](PROP_I_REALIZATION.md), [STATE.md](STATE.md) and retained
Lean scope harnesses explain the current boundaries. The [migration note](HISTORICAL_FILE_REFACTOR.md)
records the library boundaries and nine ownership corrections.

`lake env lean scripts/inspect_graphs.lean` recovers diagrams in figures.md
from the current files. Primary compiled uses now include Lemma I in Lemmas II/III, Lemma II in
Lemma III, the corollary approximation chain, and Laws I/II in the printed
composition results. The source evidence and formal uses have different scopes:
these uses prove the stated conditional reconstructions, not every clause of
Newton's general assertions. Graph omissions are coverage limits, not evidence
of absence in Newton.

## Work order

1. **Lemma I: checked conditional increment, 7 October.** The formerly
   empty namespaces now prove the positive-difference contradiction, with
   terminal lower comparisons supplied independently of equality. The
   before-end forms require a positive time window and construct an actual
   sample. Rational nonnegative terminal differences are zero. The exact
   NATP00090 par12–13 squeeze occurs inside De Motu Lemma 2; it is an editorial
   comparison, not that witness's numbered Lemma 1 or an invented Theorem 1
   citation. Its quadratic/mechanical enclosure premises remain supplied.
2. **Lemmas II–III: checked conditional geometric passage.** Actual finite
   rectangle unions have side-product areas under explicit partial area
   rules; adjacent-cell separation is proved, including repeated nodes.
   Given an assigned rational curved area, geometric inclusion derives its
   enclosure, absolute approximation errors and, if positive, unit ratios to
   that fixed area. Equal-width telescoping and unequal-width maximum estimates
   remain separate. Both editions actually use their Lemma I contradiction;
   Lemma III uses its Lemma II enclosure. General area existence, non-rational
   areas and ratios between two varying areas are still open.
3. **Corollaries and composition: checked restricted chain.** Corollary I
   uses the edition's Lemma III area theorem. A separate endpoint-rectangle
   cover estimate, supplied uniform continuity and shrinking mesh give
   two-sided rational chord/supporting-segment approximation through
   Corollaries I–IV. The covers are not staircase perimeters. Supporting
   cells are not identified as actual tangents; their enclosed area and
   arclength are not proved. Laws' Corollary I now uses separate edition-local
   inertia and calibrated additive-impulse predicates. Mechanical premises
   are supplied, not proved; the 1687 dependency interpretation remains
   distinct from 1713's explicit Law II/I citations. De Motu witness models
   are not silently replaced by printed laws.
4. **Proposition I's historical proof.** Use those checked historical results
   in AreaLaw.lean to justify Newton's finite construction, the passage to the
   supplied trajectory and swept-sector area proportionality. Prove B where
   needed for that passage. Distinguish period-appropriate premises from
   additional modern regularity. De Motu's unnumbered limiting passage and
   its two revision witnesses must not inherit the printed Lemma III citation.
   The printed editions now actually use their own Laws' Corollary I in the
   equal-triangle step; a common positive half-plane derives radial separation
   and ordinary finite union area. The passage from those finite polygons to
   the given curve is still to prove. The user explicitly requires at least
   one historical proof for the active Proposition I goal; the finite result
   and modern supporting proofs do not complete it. Commit library additions
   and newly needed historical transcriptions separately from proof changes.
   A dependency must occur in the compiled proof/type where mathematically
   used; importing a file alone is insufficient.
5. **Applications and extensions after the general Proposition I proof.**
   Finish the actual Euclidean Kepler 1/r² sampling instance using the retained
   regional confinement results. Apply the general theorem; do not build an
   independent force-specific proof. Then address window gluing and partition
   independence, and the weaker force classes, according to explicit scope.
   Continue Propositions II, III and IV in their own source order, without
   treating an application or a finite model as a completed historical proof.

If a premise cannot be justified, record the precise remaining implication
and continue only an independent obligation in this order. A failed tactic
does not prove an obstruction. Prefer one consequential increment to a new
inventory, wrapper family or completed quantity.

## Retained supporting work and deferred obligations

Do not rebuild or discard the verified construction:

- ModernLib/Polygon/GeneralForceGrowth.lean, RegionConfinement.lean and
  GeneralForcePrefix.lean use regional force contracts with derived actual,
  coarse, shadow and completed-curve confinement. The whole-plane premise
  has been removed. The Euclidean Kepler instance remains deferred.
- GeneralForceEndpoint.lean, GeneralForceTime.lean and GeneralForcePolygonCurve.lean
  retain endpoint/prefix realizations, agreement at dyadic times, whole-edge
  control and the harmonic specialization. General interior-time agreement,
  joining windows and arbitrary partition independence remain open.
- GeneralForceArea.lean proves local constructed-curve fan proportionality on
  all intervals. GeneralForcePathRegion.lean and GeneralForcePathContent.lean
  ground the actual nonnegative between-path content and its decay. Ordinary
  sector-union identification and the historical limit argument remain open.
- GivenTrajectoryArea.lean proves fan proportionality and B for a supplied
  state curve under Consistency. Its independent rational representation,
  candidate-arrival membership, cell residual and shrinking source budget are
  additional premises. Deriving that residual/rate from independently stated
  motion laws is still a modern supporting task; it cannot be imported as a
  primary historical proof. GivenMotionComparison.lean contains the reusable
  finite stability comparison.
- ModernLib/Foundation/Polygon/BinaryLift.lean supplies the shared lift used
  by completed pairings, secants and fan addition. The former D.4 requirement
  is retained: reuse it instead of proliferating operation-specific lifting
  kits. It belongs in ModernLib after the refactor.
- Constructed velocity/acceleration secants, tangent triangles and harmonic
  potential increments are retained modern support. General radial potential
  steps, unrestricted rates, non-Lipschitz uniqueness/existence, class-(d)
  counterexamples and the centre-at-infinity time map remain deferred.
- Boundary/action arguments remain a separate diagnostic layer. General
  action/potential investigations and former review housekeeping do not
  supersede the historical proof order. No universal constant is assumed.

Four root-only Contact/comparison modules were retired: Bounds, FiniteSums,
AreaCoefficient and Comparison.Routes. Their conditional coefficient/contact
results are preserved in Git rather than represented as live APIs. CircleCompare,
Polygon.Contact, diagnostics, harmonic specializations and active construction
remain. Given-motion and combined rectangle/supporting-boundary modules now
have real applications in the anachronical sections of AreaLaw, LemmaIII and
LemmaIII/CorollaryIV. These applications neither identify ordinary sector area
nor complete the historical chain.

Former API/source checks and checkpoint notes are preserved in Git. Use the
one short VERIFICATION.md and the retained Lean harnesses. Git, maintained
Markdown and historical Lean files are authoritative; do not introduce
replacement bookkeeping formats or count-based completion metrics.

## Verification and handoff discipline

Run the current README checklist: default build and all four library targets,
direct compiled axiom/taint inspection, graph inspection, archive hashes and
whitespace checks.
For touched proofs, run the applicable existing Lean scope harnesses under
research/verification. Read historical statements/proofs in their owning files.
Reader Markdown can be rendered with pandoc on demand; generated whole-library
documents and checked-in reader PDFs are removed.

Use Lean 4.34.1 core/Std only, no mathlib, no sorry and no project axioms.
Delegated implementation remains sequential v6 Sol/Luna under AGENTS.md.
For the 7 October groundwork increment the user explicitly authorized one
final Astra review, overriding the earlier prohibition for that review.
Preserve unrelated worktree changes. Commit only verified increments under
the requested Sol6.1 identity and push as authorized. Update STATE.md and the
owning source/scope notes when the result changes them. Measure progress by
discharged historical obligations, not counts, relocation or wrapper names.
