# Overnight Newton formalization, 3–4 October 2026

The user's 3 October instruction authorizes overnight work, in the order
Proposition I, II, III, IV, for **De Motu, 1687, and 1713 separately**.
The original overnight endpoint was 07:00 Europe/Madrid on 4 October
(05:00 UTC). The user's daytime continuation supersedes that endpoint.
Keep advancing verified bounded increments; the goal is complete only when
its mathematical objective is achieved, not when a clock deadline passes.
At most one subagent works at a time. Earlier overnight instructions permitted
occasional Astra opinions; the subsequently supplied AGENTS.md instruction
sets the current policy to gpt-6-sol implementation and gpt-6-luna checks,
with no new Astra work. Earlier reviews remain recorded below.

## Baseline and preservation

At start: master at `381d5e9`; 319 catalogued theorem declarations in 31
modules. Both Lean 4.19.0 builds, 245 reference/axiom checks, and the evidence
graph check passed in the preceding status turn. The worktree already contains
the 1 October proof/documentation/rendering corrections. Preserve them and
the unrelated conversation-export deletion and replacement. Do not stage
conversation exports. No mathlib or additional external dependencies.

## First bounded target: finite Proposition I in all three stages

The user's follow-up makes the main target explicit: **the area between the
impulse polygon and the actual trajectory over the same time interval**.
It must appear separately in all three Theorem 1 / Proposition I interfaces.
This is not the Kepler sector area swept by a radius from S. The unsigned
triangle-sum correction below supports the finite area law but does not itself
control that polygon–trajectory defect. Identify the geometric region and its
enclosure budget first; a supplied curve, a curve constructed by convergence,
and a finite finer polygon are three different objects.

The existing `Polygon/Finite.lean` construction proves a common oriented
triangle area for every impulse history, conditional on two explicitly named
Euclidean identities. It has no theorem about the **unsigned** triangle sum
and no separately named stage-local finite theorem. `CentralSchedule.lean`
supplies a more general rational position-dependent-field construction; it
does not remove those presentation and unsigned-area obligations.

Extend the existing finite construction in place. Define each triangle's
doubled unsigned area by `Int.natAbs`, derive its constancy from the checked
oriented identity, and prove that the finite unsigned sum is its count times
the first unsigned area. Derive the cross-multiplied area/time ratio for
positive equal cells. This does not identify polygon sums with an overlapping
sector union, construct a curve, or justify an infinite refinement.

Expose this finite statement separately in the De Motu, 1687, and 1713
namespaces. Each module must cite only its stage's passages, name the two
Euclidean identities as supplied geometric premises, and leave the stage's
limiting clause outside the proved finite statement. De Motu keeps the two
witnesses distinct and does not acquire retrospective I–IV numbering.

May assume: the existing finite recursion and its checked one-step area
identity; elementary integer/natural-number arithmetic; explicit Euclidean
construction premises. Must not assume: a limiting curve, force identification,
geometric sector enclosure, unsigned=sum-of-signed without a sign premise,
or a theorem imported from a later textual stage.

Acceptance: both library builds; catalogue and graph/reference checks; all
generated references elaborated with no sorryAx/project axiom; exact Lean
examples for positive orientation, negative orientation, radial degeneracy,
rest/zero impulse, and zero counts. A negative-orientation instance must
refute equality of signed and unsigned sums. A deliberately false variant in
a temporary Lean file must be rejected. Label the result Lean-checked finite
reconstruction, not a complete historical proof or VERIFIED-CLOSED under
the full multi-agent numerical protocol.

Pre-registered instances: lattice p=(1,0), q=(1,1), zero impulses gives signed
and unsigned sums 3 for three cells; p=(1,0), q=(1,-1), zero impulses gives
signed sum -3 and unsigned sum 3; p=(1,0), q=(2,0) with radial impulses has
unsigned sum zero; zero counts always give zero. Nonzero equal time cells
are explicit in the area/time wrapper.

## Remaining queue and stop rule

The user's additional clarification prioritizes the **unsupplied-curve
construction variant**. Supplied-curve enclosure theorems are diagnostics
only. The main forward theorem must construct the trajectory and its region
of comparison; assuming that curve leaves the central target open.

After the finite three-stage increment, advance Proposition I's P3 finite
stability/refinement comparison, beginning with the harmonic field. A proved
special case must retain its modern regularity and arithmetic premises.
If a missing historical premise cannot be discharged in a bounded increment,
record the exact gap and continue independent work on the next proposition;
do not spend the overnight window repeating source audits.

For II and III, retain the current bounded De Motu absence findings until an
actual same-stage antecedent is recovered. Never fabricate an analogue from
1687/1713. For IV, preserve all three different finite/limiting routes.
The action hypothesis is a separate open diagnostic and is not a priority
in this overnight run.

## Result checkpoints

Astra's bounded adversary-first review found no counterexample to the exact
finite unsigned block-sum claim and compiled a generic proof independently in
`/tmp/prop_i_adversary.lean`. Its periodic inward-kick example demonstrates
repeated coverage, so the sum is explicitly counted with multiplicity. It also
checked a negative orientation, radial degeneracy, rest and zero counts; a
false signed-area assertion was rejected in a separate temporary Lean file.
This review is about the pinned finite statement, not the forthcoming full
repository implementation and not trajectory realization.

The extended `Polygon/Finite.lean`, all three stage modules, and the explicit
polygon–trajectory-defect interfaces passed both builds and reference checks.

First increment independently verified (21:36 UTC): 346 catalogued theorem
declarations in 35 modules; both Lean builds; all 272 reference/axiom checks;
graph validation (77 nodes, 68 edges, 246 passages); evidence/rendering negative
controls; all source checksums; whitespace check. Only standard Lean axioms
occur. A fresh `Std` direct-determinant check reproduced the two-lobe example
with equal signed/unsigned Kepler areas but positive absolute patch budget.
The main unsupplied-curve construction remains OPEN. See PROP_I_PATH_DEFECT.md.

Commit `d182f02` checkpoints the pre-existing 1 October proof/documentation/
rendering corrections, without the unrelated conversation exports. Commit
`29703ae` records the three-stage finite/defect increment separately.

## Next bounded construction step: harmonic common-time refinement

Implement `Polygon/HarmonicRefinement.lean`, using actual `CentralSchedule.cell`
with the SAME `linearField w`, initial state s=(x,v), and total duration 2h.
Compare a coarse cell 2h with two fine cells h. Write y for the first fine
position, z for the fine endpoint, and X for the coarse endpoint. The two
polygons need not share terminal position, so the explicit connector z→X
closes their comparison; it is not an additional mechanical cell.

Pin: prove the exact local position and velocity mismatches by core rational
arithmetic. Fine-minus-coarse position is `-h²*w*y`; fine-minus-coarse velocity
is `h²*w*v + h³*w²*y`. The main signed doubled area is the closed boundary
x→y→z→X→x, not its Kepler sums. Because x,y,X are collinear, this boundary
reduces to triangle y,z,X. Prove its exact value `-h³*w*det(x,v)`. In particular
coarse and fine Kepler sums agree by centrality while this closed defect can
be nonzero. No actual trajectory is supplied or constructed in this local
step; its use is a finite comparison needed for the primary construction.

Allowed alternative: exact position mismatch plus the closed-boundary/triangle
and cubic signed-area identities if velocity expansion exceeds the bounded
unit. Record any remaining norm/accumulation obligations. Must not equate the
absolute signed gap with a global multi-lobe area, or sum local estimates as
if two evolving global polygons shared all cell initial data.

Pre-registered exact instance: w=1, h=1/2, x=(1,0), v=(0,1). Then y=(1,1/2),
z=(3/4,7/8), X=(1,1); the closed doubled defect is -1/8 and its absolute size
1/8, while the two Kepler doubled sums each equal 1. Validate with Lean decide
and a deliberately false zero-defect variant. This is finite construction,
not proof of harmonic convergence or a curve existing at all Euclidean times.

Second increment checked: `HarmonicRefinement.lean` proves BOTH mismatch
formulas, the closed-boundary triangle and cubic area identities, equal Kepler
sums, nonnegative local absolute magnitude, and all pinned values. Both full
builds passed; 360 theorem declarations in 36 modules; 286 reference/axiom
checks passed with only standard logical axioms and no sorryAx/project axiom.
The first reference command was started before the new root import finished
building and failed on unknown names; the correctly ordered rerun passed.
The deliberately false zero-defect instance was rejected. No curve is assumed
in the local finite comparison; global accumulation/realization remains OPEN.

Next bounded obligation: rational absolute-value and triangle estimates needed
to accumulate harmonic refinement errors. Search/extend the existing Fraction
arithmetic rather than introduce a duplicate rational system. Then derive
finite perturbation/schedule comparison; keep nonnegative path-area control
separate from positions and the still unconstructed actual trajectory.

Third increment checked: Fraction absolute magnitude respects represented
rational equivalence, products, signs and the triangle inequality; weak-order
transport/addition/multiplication handles zero factors. A strict cancellation
example compiles. The harmonic local absolute defect now uses this common
operation and is exactly the magnitude of its cubic coefficient. Both builds
and all 301 references pass; 375 theorem declarations in 36 modules; only
standard logical axioms, no sorryAx/project axiom. The library rebuild was run
to completion before the explicit-target and reference checks.

Current next task: add coordinate L1 point/state estimates, derive the actual
harmonic cell's one-step perturbation bound, and use it in finite schedule
comparison. These are construction estimates for the primary unsupplied-curve
variant. They are not a geometric area definition or a continuum realization.

Commit `b999b53` records the harmonic local comparison; `fd9f517` records the
absolute/triangle arithmetic. The current date is now 4 October locally; the
overnight endpoint remains 07:00 Madrid / 05:00 UTC, not the date rollover.

## Finite perturbation target pin

Construct coordinate L1 magnitudes for represented points and position/velocity
states, using Fraction.abs. Establish nonnegativity, invariance under rational
value equivalence, the triangle inequality, and scalar multiplication. This
norm is a chosen coordinate diagnostic, not a Euclidean area or a physical
sum of unlike dimensions without calibration.

For the actual harmonic cell with parameters w,h, let

    kappa = (1+|h|)*(1+|h|*|w|).

Prove stateNorm(cell(linearField w) h s) ≤ kappa*stateNorm(s). Prefer a finite
drift bound followed by a finite kick bound. Prove that subtracting two actual
cells is rationally equivalent to applying the same linear cell to the state
difference, then deduce the one-step perturbation/Lipschitz estimate. Signed
and zero parameters are allowed because the bound uses magnitudes. No modern
ODE or analytic existence theorem is permitted. Do not assume stability,
linearity or norm compatibility as fields; derive them from the actual cell.

Gate: Lean compilation with actual parameterized theorem signatures, exact
examples at h=0 and the pinned w=1,h=1/2 state, and a false norm-cancellation
control rejected by Lean. If the full perturbation step exceeds this unit,
deliver the complete point/state norm estimates with the exact remaining
cell bound recorded. This is finite quantitative construction support, not
an assumed or realized trajectory. Parent integrates source ledger and runs
both full builds and reference checks after the implementation agent ends.

Fourth increment checked: `PointBounds.lean` and `HarmonicComparison.lean`
complete the full pin, including the derived actual-cell amplification,
difference identity and perturbation estimate. The coordinate diagnostic needs
unit calibration for physical interpretation. Both full builds and all 322
references pass; 403 declarations in 38 modules, only standard logical axioms,
no sorryAx/project axiom. Exact zero-step and pinned controls pass; the false
norm-cancellation control is rejected. Global iteration, construction of the
trajectory and the intervening-area geometry remain open.

Next pin: compare n actual coarse cells of duration 2h with 2n actual fine
cells of duration h, from the same initial state and field. Derive the local
state truncation magnitude from the checked mismatch formulas, then propagate
it through the actual cells. An explicit finite recurrence or weighted sum is
acceptable as the first global bound; uniformity as the mesh shrinks is a
separate next obligation. Do not treat signed Kepler cancellation as control
of the nonnegative area between the evolving polygons.

Commit `875dc53` records the fourth increment. An occasional sequential Astra
review found no flaw in the proposed local truncation factor or global
recurrence. Its paper derivation suggests the following next uniform target,
whose full Lean proof remains OPEN: for h>0, n≥1, W=|w|, T=2nh and
T*(1+W)≤1/2, the actual state error is at most `3*T*h*W*stateNorm(s)`.
The arithmetic route uses a finite product estimate
`product(1+a_j)≤1+2*sum(a_j)≤2` for nonnegative increments of total at most 1/2.
Only its cross-multiplied induction step has yet been checked in a temporary
Lean review file; the whole product and uniform error claims must be compiled
before entering the formal-result ledger. Dyadic telescoping and between-node
control, explicit realization and unsigned intervening-area geometry follow
separately. This imports neither a supplied trajectory nor a modern ODE theorem.

Fifth increment checked: `HarmonicAccumulation.lean` derives the complete
actual local/global recurrence pin, including schedule correspondence and
equal elapsed times. Both full builds and all 342 references pass; 445
declarations in 39 modules, standard logical axioms only, no sorryAx/project
axiom. Exact one/two-block errors are 13/16 and 173/256; the false endpoint
equality is rejected. The recursive budget is a finite state estimate.
Its uniform bound and the separate nonnegative intervening-area accounting
remain the next construction obligations.

Commit `dc3e9b7` records the fifth increment. Parent's next bounded arithmetic
unit uses positive common denominator D and a finite list of nonnegative
integer increments a_j. Let S=sum(a_j) and P=product(D+a_j). Prove by finite
induction `P*(D-S)≤D^(length+1)` and deduce `P≤2*D^length` when `2*S≤D`.
Package the latter as a Fraction amplification estimate for P/D^length,
with finite factor/list identities needed to transport the actual harmonic
powers. Test empty/zero increments, a boundary case, and reject a false
uniform bound when the small-total-increment hypothesis is removed. These
are elementary finite arithmetic estimates; no completeness is supplied.

Sixth increment checked: `Common/FiniteGrowth.lean` completes the finite
cofactor and small-total amplification pin, including list/replication
identities. Both builds and all 360 references pass; 464 declarations in 40
modules, standard logical axioms only and no sorryAx/project axiom. The empty,
zero and boundary controls compile. The deliberately false bound without
smallness is rejected. No historical dependency is attributed to this modern
arithmetic support. Next transport actual harmonic powers and close the
mesh-uniform state estimate before constructing Cauchy data and unsigned strips.

Commit `6437bb1` records the sixth increment. The next sequential implementation
pin is `HarmonicUniform.lean`: with h≥0 and T=2nh, derive actual coarse/fine
power bounds ≤2 under T*(1+|w|)≤1/2, hence their state bounds and the proposed
actual error bound `3*T*h*|w|*stateNorm(s)`. Zero blocks and zero steps remain
explicit. The boundary control w=1,h=1/8,n=1 has T=1/4, proposed actual state
error 145/4096 and final bound 3/16; independently check these numeric pins.
Without smallness, w=1,h=1,n=1 has fine amplification 16, so a false ≤2 claim
must be rejected. The implemented theorem must derive its bounds from the
actual cells and finite factors, not take them as supplied fields. A stable
compiled uniform power/state subset is acceptable if budget closure exceeds
this bounded unit; the exact remaining recurrence lemma must then be recorded.

Seventh increment checked: `HarmonicUniform.lean` completes the full uniform
power, state and actual error pin for every n, including zero. The parent
added the explicit equality of both elapsed times with displayed T and named
the calibration of the small-time threshold. Both builds and all 381
references pass; 514 declarations in 41 modules, standard logical axioms only,
no sorryAx/project axiom. Boundary and zero controls pass; the unrestricted
power-two bound is rejected. Next address unsigned geometric patches and
construct Cauchy data. The main trajectory existence claim remains open.

User pause: sleep until 04:02 Madrid on 4 October (02:02 UTC). All workers are
idle. The seventh increment is checked and saved before pausing. Resume with
the unsigned area-between-paths target, followed by Cauchy construction; do
not supply a curve or confuse this area with Kepler area. The user requested
this pause explicitly; the overnight endpoint remains 07:00 Madrid.

User resumed on 4 October at about 08:04 Madrid / 06:04 UTC. This revokes
the pause and authorizes continuation beyond the original overnight window.
The goal tool still reports paused; its interface cannot set an active status.
Continue the saved mathematics without treating this tracking state as a
mathematical blocker. Commit `7c52a0f` contains the seventh checked increment.

Later daytime refresh: the goal now reports `active`. The user's continuation
instruction remains in force; the original overnight endpoint is superseded.

The user explicitly said to keep going through the day. Next bounded area
pin: derive rational determinant/triangle magnitude estimates from PointBounds,
including nonnegativity and translation/orientation compatibility. A finite
unsigned triangle-patch sum must retain both opposite lobes. Then use these
estimates for actual equal-time coarse/fine path patches; no curve is supplied.

Eighth increment checked: `TriangleBounds.lean` proves the full rational
determinant/unsigned-triangle pin. Both builds and all 395 references pass;
531 declarations in 42 modules, standard logical axioms only, no sorryAx/
project axiom. Positive/negative orientation and cancellation controls compile;
Lean rejects the false unsigned-equals-signed assertion. These are finite
patch estimates. Next construct a geometric enclosure for actual coarse/fine
path regions and derive its nonnegative mesh-dependent cover-area budget.

Commit `0dfcfb1` records the eighth increment. Ninth pin: derive convex
rational interpolation and coordinate-square containment, then enclose the
actual two matched half-cell patches of each evolving coarse/fine block.
Under the existing small-time condition, with T=2nh and M=stateNorm(s), use
the constructed radius `R=h*M*(4+3*T*abs(w))` about each coarse start.
Prefix state/error bounds must be derived from the final time hypothesis.
The summed square-area budget `4*n*R²` should equal
`2*T*h*M²*(4+3*T*abs(w))²`, be nonnegative and cover the actual matched point
regions. It counts squares with multiplicity and is not the region's actual
area. Boundary control w=1,h=1/8,n=1 predicts R=19/16 and cover area361/64;
independently verify the values and reject a false too-small corner cover.
No curve is supplied. If the global prefix proof exceeds the unit, retain a
compiled generic enclosure and actual one-block result with the remaining
lemma named exactly. Completion and content/area identification stay open.

Ninth increment checked: ConvexCover and HarmonicCover derive the full finite
matched-patch square enclosure and budget formula. Both builds, catalogue,
graph and all 428 references pass sequentially; 590 declarations in 44
modules, standard logical axioms only and no sorryAx/project axiom. Zero and
boundary controls pass. Lean rejects the deliberately false eighth-radius
coordinate-square cover. The quarter-radius L1-ball control concerns a
different point set; no quarter-radius square failure is claimed.
Next freeze this increment for a sequential independent arithmetic holdout,
then derive dyadic finite Cauchy data from actual schedules. Completion,
partition independence and actual polygon-trajectory area remain open.

Commit `15d50ad` freezes the ninth increment. A sequential Luna verification
is running the disclosed fresh-input arithmetic holdout; no implementation
changes are made during that check.

The sequential check finished successfully: both frozen-snapshot builds,
all 428 references and the third fresh signed two-block arithmetic comparison
pass. The altered-radius comparator is rejected as false. Two earlier harness
attempts are burned, not proof-code failures or passing evidence. Unchanged
sources, logs and birth/contact/hash records are archived under
`research/verification/harmonic-cover-2026-10-04/`. The check's shared model,
integer/kernel layers and formula/geometry boundary are explicit.

Tenth target pin: actual dyadic endpoints, not a supplied curve. For rational
T>=0, set H_j=T/2^j and D_j to the output of 2^j actual harmonic end-kick
cells H_j from s. Under T*(1+abs(w))<=1/2, derive the correspondence of
D_j,D_(j+1) with coarseAt/fineAt at h=H_(j+1), n=2^j, preserving rational
value equivalence and actual elapsed time T. Then derive adjacent error
at most 3*T*H_(j+1)*abs(w)*M and, for every finite k, error between D_(j+k)
and D_j at most A/2^j, A=3*T²*abs(w)*M. Derive a positive-tolerance modulus
by finite integer arithmetic, and construct the endpoint's Cauchy-name data
with its Cauchy proof. A structure field asserting that D_j is Cauchy without
deriving it is forbidden. No limit point, curve, completeness, generic ODE
theorem or force regularity is supplied. Existing Fraction/cell/PointBounds
helpers must be extended rather than introducing a second arithmetic stack.

Licensed bounded fallback if full tolerance construction exceeds the unit:
compile actual dyadic schedule identification and arbitrary-finite-gap bound,
then name exactly the missing modulus/completion lemma. The production-side
boundary control w=1,T=1/4,s=((1,0),(0,1)) has adjacent error145/4096 at j=0,
adjacent cap3/16 and tail cap3/8. Zero time must give the initial state in
value equivalence at every level. A false level-0/level-1 equality must fail.
Any discarded nonnegativity/small-time premise or silently assumed limit
disqualifies the route. These names concern fixed rational-time endpoint data;
a coherent continuous trajectory and its nonnegative actual intervening area
remain further obligations, separate from Kepler swept area. Any spec error
is recorded before correction; no historical stage label is promoted.
