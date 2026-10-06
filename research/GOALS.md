# Approved programme: three Newtonian proof architectures

Approved in conversation, 22 September 2026. The targets are De Motu, 1687,
and 1713. The printed-edition targets are Book I, Section II, Propositions
I–IV; De Motu requires an explicit correspondence search, not retrospective
proposition numbering. Proposed 1694 and 1726 remain comparison witnesses.

Latest user direction, 6 October: prioritize Proposition I, then II, III and IV
in all three stages, taking the trajectory's existence as an explicit
postulate. In Lean, provide the trajectory as a curve parameter; its physical
laws and any regularity assumptions must remain separately stated. Do not
postulate that the curve equals the limit of Newton's polygons.

The primary conclusion (A) is the Kepler swept-area law: equal swept sector
areas in equal times, more generally areas proportional to elapsed times.
The separate quantity (B) is the nonnegative region BETWEEN polygon and
given trajectory. Its decay is a proof obligation controlling Newton's
approximation, not Proposition I's conclusion. Neither area proportionality
nor vanishing between-path area is included in the existence postulate.
Equal swept areas alone establish neither path agreement nor (B).

This supersedes the 3 October requirement to construct a trajectory before
the primary proof. Preserve the verified construction as supporting work.
The existence convention is a user-authorized editorial interpretation;
do not label it an explicit postulate in Newton's text. The given-curve
lemmas can now serve the primary proof, with their remaining premises visible.

## Historical derivation

For each target, reconstruct the available definitions, laws, invoked earlier
results and imported mathematics. Prove the finite constructions and limiting
steps where derivable. Every historical dependency needs its passage, witness,
URL, classification and confidence. Later editions cannot silently supply
earlier premises. Historical proof, coordinate example and diagnostic
reconstruction must be named separately.

The four targets are the central-force area law, its converse, relative motion
and force composition, and uniform circular-force comparison. Missing De Motu
counterparts are to be reported, not supplied by analogy. Existing M1–M4
results support this programme but do not discharge it.

## Instants, intervals and trajectory realization

An instant marks an interval boundary. Restriction of an existing trajectory
to subintervals is distinct from constructing a trajectory by joining segments.
Investigate these obligations separately:

1. Finite joining: common endpoint positions; matching velocities for an
   impulse-free join; or a specified mechanical velocity jump.
2. Subdivision and refinement: identify which old vertex, time and mechanical
   data survive a refinement, rather than assume nested polygonal motions.
3. Realization: the primary historical route takes an existing trajectory as
   data. Identification of Newton's approximations with that trajectory,
   uniqueness where used, and independence of partition remain separate
   questions. Constructing trajectories is retained in the supporting route.
4. Limits: distinguish convergence of scalar areas, positions, velocities and
   impulse/force data. A sector-area limit does not itself provide a trajectory.

The boundary-orientation analogy motivates explicit cancellation identities;
Gauss's theorem is not an imported historical premise. Finite sampled paths
are a first diagnostic interface, not continuous motion or a limit theorem.

## What counts as a failure

Record an exact proposition, its permitted premises and source correspondence.
Distinguish unfinished proof work, missing textual justification, a countermodel
to a specified implication, and a proved obstruction under stated assumptions.
Lean rejection alone proves none of the latter. Test weak classical repairs
in a separate reconstruction layer. Successful classical repairs are results.
Do not call an open bridge irreducible without a supporting theorem.

## Action hypothesis and its possible rejection

For substantive joining/refinement obstructions, derive any proposed residual
from the quantities involved before assigning it the dimension energy × time.
An action-valued quantity can depend on the motion; a fixed universal action
constant is a stronger claim. Test positivity, finiteness, partition stability,
system independence and action-rescaling freedom separately.

Any necessity theorem must state the admissible class of repairs and show why
they require a constant rather than simply assume one. A free normalization
does not determine a physical value. Identifying a parameter with Planck's
constant requires a further physical bridge. Classical repairs, no action
dimension, and an undetermined scale are all admissible outcomes.

Newton's revisions motivate comparison; they alone prove neither inconsistency
nor psychological uncertainty. The empirical limits of classical mechanics
do not imply an internal contradiction in its mathematical models.

## Deliverables and validation

- Three source-qualified proof maps and a statement/premise ledger for I–IV.
- Checked finite joining/subdivision results and discriminating counterexamples.
- Explicit realization/refinement obligations, with conditional results marked.
- A separate assessment of the action hypothesis supported by those results.

Use Lean 4.19 core/Std only, empty external dependencies, no `sorry`, and no
post-Newtonian theorem filling a historical gap. Run both build targets,
reference/axiom inspection and evidence-graph checks. Compilation is not
certification that supplied premises have been derived. Preserve unrelated
conversation archives. Work and verification agents run sequentially according
to AGENTS.md; no bulk downloads are needed for the first finite obligations.

## Historical file architecture, selected 6 October

Use one file per historical result, with separate edition/witness sections;
each includes exact Latin and its corresponding formal definitions and proof.
Move support according to mathematical content into BarrowLib, ClassicsLib
and ModernLib. The concrete migration plan and current ownership problems
are recorded in [HISTORICAL_FILE_REFACTOR.md](HISTORICAL_FILE_REFACTOR.md).
This refactor changes presentation and ownership, not the proof-status bar.
