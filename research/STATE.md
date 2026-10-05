# Research state

A.6 has its first finite confinement mechanism in RegionConfinement. A single
invariant retains |v|<=|v0|+t*B, |x|<=|x0|+t*V and the conserved areal
product, V=|v0|+T*B. Each drift arrival lies inside the ball/annulus before
the bound on that band is used to evaluate force. Positive speed and
r0*V<=|ell| give the inner radius; r0=0 covers rest and radial motion.
Actual/coarse runs and both coarse-field shadow arrivals inherit the same
bound, without a supplied confinement trace or whole-plane force premise.
The force-comparison theorem now accepts membership only at its two points;
shared pointwise cell estimates use exactly that comparison. A live calibrated
cell client derives both arrival certificates before applying it, with a proper
annular oracle control that excludes the origin. Conditions and completed-force
localization, completed curve confinement and an actual Euclidean Kepler oracle
are still required to finish A.6. Task E and new completed quantities have not
started. See the [finite confinement checkpoint](verification/region-confinement-2026-10-05.md)
and [regional comparison checkpoint](verification/regional-cell-comparison-2026-10-05.md).

GeneralForceGrowth now derives all three actual/coarse/shadow sample bounds
from the whole-plane Lipschitz contract and initial state. Inward samples
vanish at the centre. With E=2*E0 and r0=|x0|+tau*|v0|, the shared finite
recurrence gives M=2*(r0+tau*T*E), shadow radius R=M+T*M/tau and B=L*R+E.
The resulting conditions feed the existing motion and geometric constructions;
no separate bound along a run is supplied. The length cap is invariant under
positive time-unit rescaling. This retains global_region and excludes singular
Kepler laws; Task A.6 confinement is the required next repair. It neither
proves the constructed-curve area law nor changes completion scores. See the
[derived-bound checkpoint](verification/general-derived-bounds-2026-10-05.md).

The user-requested [theorem-growth study](THEOREM_PROLIFERATION.md) compares
the handoff's 793 declarations with 1,371 at the study snapshot. Most additions build the
elementary foundation or Proposition I's modern construction; count-based
classification also mislabels universal sampled results and thin quotient
interfaces. PolygonValues now shares finite-vertex polygon alias proofs, and
GeneralForcePolygonCurve constructs the general whole-edge map, preserving
existing names and explicit sample premises. MatchedRegion now shares closed-cell connector and cover geometry between the
retained harmonic and actual general regions. Their completed outer contents
have derived geometric decay. The next obligations include general radial potentials and their curved steps,
the D_mesh relation, local confinement/gluing and general interior-time E/G agreement. One sequential Astra architectural review
was explicitly requested for this study; the usual sequential v6 policy
continues afterward.

**Caveat on "general" (5 October).** Every general-force result below
rests on the premise `global_region : ∀ p, o.region p`: the sampled force is
Lipschitz on the whole plane. That excludes every law singular at the centre,
`1/r²` first of all, so these results do not yet instantiate to the laws
Proposition I was written for; the harmonic field is the only instance built.
Replacing the premise by derived region confinement is the required first
repair (handoff Task A.6), and the area law for the constructed curve itself
is not yet stated for any instance (handoff Task E).

Current handoff execution (Sol 6.1, 4–5 October): D.1, Task A's finite
interface/estimate increments and D.2 are committed. The [force design](GENERAL_FORCE_DESIGN.md)
constructs force values from uniform rational samples. GeneralForceEndpoint
now constructs fixed-time motion Cauchy names/values for globally compared
Lipschitz central samples, with a calibrated short window and explicit bounds
at actual coarse and first-half shadow sample locations. Geometric force
precision and actual adjacent errors are derived; the harmonic instance derives
those force bounds and agrees with its old endpoint value. GeneralForcePrefix
and GeneralForceTime now construct Cauchy prefix names and a continuous local
state/position map on BinaryTime. Actual grid sample bounds derive optional-cell
and same-grid estimates; address independence precedes quotient lifting. Uniform
prefix convergence, initial/zero-time values and E/G agreement at the full
endpoint are proved. HarmonicGeneralTime derives the extra actual-grid bounds
and equals the retained harmonic maps. Local-annulus stability, restart/gluing,
derived confinement and general interior-time E/G agreement remain open. The generic geometry,
completion and binary-time infrastructure is in BarrowLib.
B.1 now proves E/G agreement at every dyadic rational time, including zero/full
window endpoints. Explicit finite addresses represent every numerator below
2^m. Actual integer-cell accumulation gives geometric error C/2^j; prefix
Cauchy control removes the index shift. Three-tick finite schedules are proved
unequal while their completed values agree. B.2 constructs actual within-cell polygon
position names, proves their phases lie inside each cell, and derives a
whole-edge distance bound tending to zero uniformly over addresses.
Both same-cell and shared-boundary aliases now agree, and the actual coarse
polygonMap descends to the same time quotient with uniform convergence.
The integer-subdivision accumulation and dyadic E/G comparison are now proved.
Explicit calibration now has weighted actual finite bounds, a shared
finite growth proof, Cauchy-gauge equivalence and positive time-unit invariance;
see the [calibration checkpoint](verification/calibrated-finite-bounds-2026-10-05.md).
HarmonicPathRegion now constructs the actual matched between-path set from
polygonMap and gammaPosition, closing rational connectors cell by cell. Its
D_mesh is the nonnegative closed lower cut of the infimum over all finite square
cover budgets. HarmonicPathContent now realizes that cut as a Cauchy scalar by
proved shrinking rational intervals, independently of the initial cover budget. A derived cover has budget 4*C²/2^m and tends to zero, including
zero time. Crossings and overlaps count once in the region; cover sums count
multiplicity. Initial endpoints agree and the final connector is included.
See the [content checkpoint](verification/constructed-path-content-2026-10-05.md).
GeneralForceSecants now proves that completed bracketing dyadic position
secants converge uniformly to the constructed velocity, including the right
boundary; HarmonicSecants gives the old harmonic-map corollary. Finite
restarted drift/kick remainders, completed secants and dyadic time nodes are
derived in BarrowLib. CompletedForce now extends the actual sampled force to
completed positions by a proved diagonal Cauchy construction. It is Lipschitz,
agrees with rational force values, depends only on position and is independent
of the precision scale. Actual prefix force samples converge uniformly to the
force at the constructed curve, with budget (A*L+3*E0)/2^j. The harmonic
extension equals completed scaling by -w and applies to the retained curve.
GeneralForceAccelerationSecants now passes finite velocity remainders to
completed dyadic velocity secants and proves uniform convergence to that force.
The bound H_m*L*(V+K) includes the final boundary; precision-offset invariance
and vanishing rounding error are derived. HarmonicAccelerationSecants gives
the retained-curve corollary. Unrestricted difference quotients remain open.
GeneralForcePolygonCurve now constructs the coarse polygon quotient from actual
run vertices and shares the finite-vertex alias/joining proof with the retained
harmonic polygon. Whole-edge error is (T*V+A)/2^m uniformly over the constructed
time domain, with actual V and the derived prefix coefficient A. The shared
initial endpoint and exact harmonic polygon specialization compile. Ordinary-
area/Kepler-area identification and the remaining classes stay open.
GeneralForcePathRegion/Content now construct the actual general closed-cell
connector union and its all-cover cut and canonical Cauchy scalar. Actual
vertex and prefix bounds derive one square per cell with budget 4*C²/2^m,
C=T*V+A; nonnegativity, zero time, decay and initial-cover independence follow.
The final connector is included. HarmonicGeneralPathContent proves exact
region and scalar equality with the retained harmonic objects. [Arg007](action-arguments/261004gpt6.1solv1Arg007.md) records the permitted
exact finite-cell potential identities and now the actual Galilean rational-
endpoint comparison. QuadraticEstimates derives the finite cubic/error remainder
and exact half-mesh bias; ParallelQuadraticEndpoint constructs endpoint Cauchy
values with position x0+t*v0+t²*a/2 at every nonnegative rational time. The
parallel potential drop and doubled tangent-deflection area are both half their
kick counterparts, with the same motion-dependent ratio. GeneralForceQuadraticSecants
now passes the finite estimate to the actual completed central curve: the
normalized departure 2*(Delta_x/H-v_left)/H converges uniformly to completed
force, with error H*L*(2V+K). Force-name Cauchy boundedness derives half-mesh
bias decay; sampling and precision-offset errors are handled explicitly. The
retained harmonic curve inherits this criterion. ConstructedHarmonicPotential now evaluates the harmonic polynomial potential
on the actual completed curve and its tangent continuation. PairingValues
shares one derived Cauchy/representative proof for dot products and determinants;
QuadraticPotentialValues composes it with existing completed secants. The finite
work identity identifies the polynomial with the harmonic force. Actual node
bounds and the shared finite second-order estimate give a uniform O(H) bound:
Delta V/H² converges to -mass*dot(a_left,a_left)/2 over all dyadic cells,
including the last one. No potential-step asymptotic is assumed. General radial
potentials, unrestricted quotients and the triangle/lobe relation to D_mesh
remain open. This law test receives no extra completion score.
GeneralForceTangentTriangle now constructs the signed doubled triangle between
the actual left curve point, its tangent continuation and the actual right
curve point. TangentTriangleValues proves its rational embedding and exact
completed identity: triangle/H³ equals half the determinant of velocity and
normalized second departure. The proved second-order bound and actual velocity
caps give error H*L*V² against det(v_left,a_left)/2, uniformly over every dyadic
cell including the last. The signed doubled triangle is distinct from unsigned
lobe area and matched-region D_mesh; their geometric identification and general
radial potential steps remain open. Completion scores stay unchanged. See the
[quadratic checkpoint](verification/quadratic-finite-parallel-endpoints-2026-10-05.md)
and [constructed second-order checkpoint](verification/constructed-quadratic-secants-2026-10-05.md).
See the [constructed harmonic potential checkpoint](verification/constructed-harmonic-potential-2026-10-05.md)
and [general tangent-triangle checkpoint](verification/general-tangent-triangle-2026-10-05.md).
The progress estimate now credits the
constructed general local time map, dyadic velocity/force-secants bridges and
actual general outer content, about
39% overall (35–46% under alternative weights); no target is discharged.
See the [general time checkpoint](verification/general-central-time-map-2026-10-05.md).
See the [completed force checkpoint](verification/completed-central-force-2026-10-05.md).
See the [acceleration secants checkpoint](verification/constructed-acceleration-secants-2026-10-05.md).
See the [general polygon checkpoint](verification/general-polygon-map-2026-10-05.md)
and [general content checkpoint](verification/general-path-content-2026-10-05.md).

Resume context: start from the [latest handoff](HANDOFF-2026-10-04-GENERAL-FORCE.md)
(4 October: general central forces, the polygon–curve defect and a foundation
library). It supersedes the [22 September handoff](HANDOFF-2026-09-22-NEXT.md)
written at the end of that Claude Code session. The earlier
[22 September handoff](HANDOFF-2026-09-22.md) records the user's defect-area
correction. Its bounded common-time/force comparison
is now recorded in [time subdivision](TIME_SUBDIVISION.md); follow the next
obligation there and in TASKS.md rather than repeating the original task.
Continued autonomous work across the programme is authorized; see
[completion criteria](CONTINUATION.md).

Latest priority (3 October user instruction): **Proposition I, then II, III,
IV, in De Motu, 1687 and 1713 separately**. Construct the trajectory in the
primary forward variant. Its main area lies BETWEEN polygon and trajectory,
distinct from the Kepler area law. See [path defect](PROP_I_PATH_DEFECT.md)
and the [overnight checkpoint](OVERNIGHT-2026-10-03.md). Zero-force support
remains useful. The harmonic construction now has a checked local common-time
position/velocity and area comparison, coordinate triangle estimates and an
actual-cell perturbation bound; see [harmonic refinement](HARMONIC_REFINEMENT.md).
Actual global coarse/fine schedule error is now bounded by an explicit finite
recurrence. Uniform refinement control, trajectory existence and nonnegative
intervening-area geometry remain separate: HarmonicUniform now derives
mesh-uniform power/state bounds and actual error ≤3*T*h*|w|*M under its named
small-time condition. ConvexCover and HarmonicCover now enclose every rational
matched half-cell patch between the actual paths in a derived square. Their
nonnegative, multiplicity-counted cover budget is
2*T*h*M²*(4+3*T*|w|)². The harmonic and globally compared Lipschitz central-force local time maps
are constructed; ordinary-area identification remains open. HarmonicDyadic now constructs
actual fixed-rational-time endpoint Cauchy data, with arbitrary finite-gap
bound 3*T²*|w|*M/2^j and an explicit positive-tolerance modulus.
HarmonicTimeComparison derives the rational-time map
of these names with uniform bound 4*(1+2*|w|)*M*|U-T| and explicit positive
delta=eps/(L+1). Identification with prefixes of one global polygon family is
now proved at dyadic rational times. Other time parameters, partition
independence and mechanical force identification remain separate.
HarmonicBinaryPrefix now constructs Cauchy data at intermediate times from
actual prefixes of one global dyadic family. Every binary address has a
derived geometric tail and explicit positive-tolerance modulus. CauchyValues
now constructs their values in a proved quotient of Cauchy names, lifts
representative-invariant bounds, and proves convergence and rational-state
embedding separation. Identification of equivalent time descriptions and a
continuous map on the
constructed time domain are now derived in BinaryTime and
HarmonicTimeRealization: actual same-grid states differ by at most
2*(1+|w|)*M times their time difference, equivalent addresses descend to the
same value, and continuity, endpoint/alias identities and zero cases are proved.
PositionValues now derives planar values and gammaPosition, preserving bounds,
continuity and time identities. Its coordinate-square predicate transfers
eventual rational bounds, and the positive sample position separation is proved.
Same-time coarse polygon names, whole-edge distance and both kinds of address
independence now construct a quotient coarse polygon map. HarmonicPathRegion
constructs its matched between-path region and a vanishing finite-square outer
content lower cut; no scalar area is supplied. Its ordinary-area and mechanical
identifications remain open; see
[the construction specification](CAUCHY_REALIZATION.md).
The first finite suite
is implemented in `Polygon/ZeroForce.lean`: actual-cell and finite-schedule
agreement with `p+t*v`, constant velocity, cross-denominator subdivision
independence, exact restart, rest and within-cell positions. A zero-defect
example distinguishes motions with different initial velocities; it is not
fixed-data nonuniqueness. See [zero force](ZERO_FORCE.md). These are rational-time
constructions with no presumed limiting curve; full Euclidean-time realization
and additional geometric/area obligations remain separate.
`Polygon/InertialControl.lean` adds the explicit small-time bound: each positive
rational tolerance has a constructed positive radius that controls both drift
coordinates uniformly in position and rational base time, including an actual
zero-force cell. This closes the pending inertial estimate.
`Polygon/InertialDefect.lean` adds signed defect cancellation: directed
determinants of inertial samples compose additively, so every finite closed
walk (explicit connector included, sample times unordered) has zero signed
doubled area, and four actual zero-force schedules with arbitrary partitions
give a vanishing boundary. Unsigned enclosure estimates and extension beyond
rational times remain open.

Action diagnostic: candidate arguments now live in
[action-arguments](action-arguments/README.md), one file per proposer and
version. Arg001 records that every checked refinement residual vanishes with
the mesh. Arg002 records that Proposition IV Cor. 1 (1713 Cor. 7 for the
family) singles out inverse-cube circles as the one power law with a common
areal velocity, checked for two circles in `Diagnostic/InverseCubeAreal.lean`.
That action is system-dependent. At the user's direction the ledger now
develops arguments *for* a nonzero constant from the Latin and Newton's
revisions. Arg004 finds that the construction's exact invariants that survive
every mesh and every force (phase area, checked in `Diagnostic/PhaseArea.lean`,
and the areal product) are actions. Arg005 traces the short-time law from
hypothesis to the 1713 force clause (finite enclosure in
`Polygon/MonotoneEnclosure.lean`). Arg006 reads the two 1713 finiteness
clauses as a bound on one local action. None fixes a value.

Order 3's constant-force rational-time position/velocity comparison is closed by
`partition_gap`; absolute polygon-strip sums remain open. Order 5
has its finite Case-1 step in `Polygon/Converse.lean`: equal oriented areas
are equivalent to a deflection parallel to the radius, with orientation, a
vertex distinct from S, and the inward sense kept as separate premises.

Order 6 (Proposition III) now has its finite step in
`Polygon/RelativeMotion.lean`, with the source map in
[Proposition III](PROP_III.md): two bodies advanced by one pair recursion, each
with its own deflection history. Corollary VI of the laws is
`corVI_relative` — any common deflection history leaves both relative
coordinates unchanged at every stage — and Law I is `lawI_uniform` — an
undeflected reference body is exactly the uniform `centreAt` motion of its
initial pair. The compositional content of the proposition is
`relative_deflection_difference`: the relative polygon's deflection is `d n − e n`.
Equal relative oriented areas make that difference parallel to the relative
radius (`relative_equal_area_central`, and `relative_rational_central` with a
nonzero radius), which is also reachable by Newton's own route through
`Converse.moving_centre_equal_areas_central` (`propIII_via_moving_centre`).
That route now explicitly adds `−e` to both histories, identifies the reduced
reference body's `.p` at time `n` and `.q` at time `n+1`, and transfers the
original relative-area hypothesis before applying Proposition II.
The six Proposition III dependency edges (Corollary VI, Law I, Proposition II,
both editions) now carry these formal references. The limiting passage from a
realized relative orbit, parallelogram composition of simultaneous forces, and
any force/mass interpretation remain open.

Order 4 is decomposed in [Proposition I realization](PROP_I_REALIZATION.md).
`CentralSchedule.lean` proves the finite area law for any central field with
unequal rational cells and gives the exact refinement identities for a varying
force. The missing premise for the ultimate curve is control of force
differences; Proposition I cites none, and Lemma X's force qualification
(1687 *regularis*, 1713 *finita … continuo augetur vel diminuatur*) is the
nearest same-stage candidate. For the harmonic field (Prop. IV Cor. 3 case),
`HarmonicStability.lean` proves an exact equal-cell invariant and
mesh-uniform bounds on speed and position: the first stability result for a
varying central force. Convergence remains open.

The approved governing target is now the three-stage formalization of
De Motu, 1687 and 1713 arguments corresponding to Book I, Section II,
Propositions I–IV: see [goals](GOALS.md). M1–M4 below are supporting work.
The first new obligation is finite joining versus trajectory realization;
the action-constant hypothesis remains separate and unproved.

New finite diagnostic: `Polygon/Contact.lean` now compiles with explicit
position/velocity/impulse contact, restriction of supplied samples, and finite
gluing results. `motion_restart` proves exact continuation from the current
vertex pair with shifted impulses. The lattice construction derives the
velocity jump and zero-impulse velocity contact, rather than assuming them.
Its counterexample gives equal swept sums and unequal next vertices under
two different inward impulse histories (-1 and -2). It establishes insufficiency
of area data for identification, not failure of existence or fixed-force
uniqueness. Continuous-time refinement and mechanical realization remain open.

New finite refinement diagnostic: `Polygon/RefinementStrip.lean` constructs
the closed area between a coarse lattice edge and a spatially compatible
two-edge fine polygon. Its determinant identity reduces that signed doubled
strip to the Euclidean triangle on the three vertices; its `Nat` defect is zero
exactly when that signed strip is zero. The compatibility condition compares
finite `motion` endpoints explicitly, and the inward example has a nonzero
strip. This is not a swept-sector claim, a common-force time-refinement law,
or a limiting-curve construction.

The new rational `Polygon/TimeSubdivision.lean` comparison makes common
initial position, velocity, constant accelerative force and positive time
subdivision explicit. Under an end-of-cell impulse convention, the fine
endpoint equals the coarse endpoint plus `h*k*a`, while terminal velocities
agree. Exact nesting therefore fails in the constructed nonzero-force example.
An explicit straight connector closes the finite polygon comparison; it is
not a further mechanical cell. This is a modern constant-force diagnostic,
not Newton's general central-force theorem.

`Polygon/PartitionControl.lean` now connects arbitrary finite common-denominator
end-kick schedules to exact velocity and position formulas. It proves
`2*A+Q=T²` and `Q≤M*T`, with `Q` the sum of squared duration numerators and
`M` an upper bound on each. Against the explicitly constructed rational
polynomial map, the endpoint residual is exactly `(Q/(2D²))*a`; its scalar
coefficient is bounded by half the largest-cell bound times elapsed time.
See [finite partition control](PARTITION_CONTROL.md).
`Polygon/PartialCell.lean` adds within-cell positions: a partial final cell
`u/D` drifted from the actual prefix state has exact residual
`((Q+u*u)/(2D²))*a`, with `Q+u*u≤M*(T+u)` when `u≤w≤M`. The next step is
rational-time convergence to that map across partitions;
`UniformRefinement.lean` already gives, per positive rational tolerance, an
explicit refinement with residual coefficient below it, and
`PartitionComparison.lean` proves that two arbitrary partitions reaching one
rational time agree once each is corrected by its own exact residual,
retaining absolute defect accounting and the general central-force existence
obligation separately.

The [Section II source map](SECTION_II.md) now identifies printed I–IV
dependencies and De Motu antecedents for I and IV. Counterparts of II/III
were not found in the inspected De Motu ranges; this is not an edition-wide
absence claim. Proposition IV's explicit route differs between 1687
(Proposition II, Lemmas V/XI) and 1713 (Proposition II, Proposition I corollaries
2/4, Lemma VII). See the [ordered obligations](TASKS.md) for continuation.

The implementation request authorizes M1–M4 beyond the earlier M1-only boundary.
Scope stays within the requested changing proof architecture. Lean 4.19.0,
core/Std only; external dependencies remain empty.

| Milestone | Checked progress | Remaining completion barrier |
| --- | --- | --- |
| M1 | Independent H4 edited witness; rational consistency model; constructed s/t² and triangle normalization; conditional bridge and force-coefficient algebra; TEI/page-anchor collation | Direct image inspection and earliest H4 chronology; curved contact construction; mechanical velocity-area enclosure; variable-force corollaries |
| M2 | Constructed finite polygon, equal-area sums, maximum-width rectangle bound, conditional sector-ratio transfer | Geometric refinement connecting the constructed polygon family to an enclosed curve; continuous-force trajectory identification is a separate open issue |
| M3 | Conditional contact/cubic inequalities, finite sums, rectangle-derived 1/2 and 1/3 coefficients, reciprocal error convergence, rational uniform N^-2 bound | General curved contact geometry and mechanical identification of the velocity-area construction |
| M4 | C44 identity; evidence-qualified proposed outline; actual-edition DAGs and generated comparison; matched constant-force route algebra; TEI/page-anchor collation including 1726 views | Direct C42 and draft-folio/image collation; general generated/sagitta limiting comparison |

**M1–M4 are not certified complete.** Compiling conditional theorems and four
reports do not discharge their displayed geometric and historical premises.
See M1.md through M4.md and formal-results.json for exact boundaries.

Sources: TEI is the machine-readable authority; identifying translations and
untranslated passages are labelled. The source-collation report records page
and facsimile targets without downloading or reading manuscript images.
Selected PDF passages were visually checked; no general manuscript-image audit
is claimed. See [collation](collation.md) and edition-comparison.md.

Validation commands are in README.md. No sorry or project axioms were added;
standard Lean logical axioms can appear in generated dependency inspection.

Unrelated conversation-export deletion/new file remain untouched. No mathlib,
cache download, toolchain upgrade, correspondence or publication was performed.

## 2026-09-28 session (arena branch, toolchain built from source; continuation)
Resumed from `f50ff14` and extended the formalisation; all Lean compiles under
the source-built Lean 4.19.0 (core/Std only, no mathlib), both build targets, and
`research/CheckReferences.lean` elaborates every reference with axiom set
`{Classical.choice, Quot.sound, propext}` and no `sorryAx`.
- Order 6 (Proposition III, two-body): `Polygon/RelativeMotion.lean` proves
  relative deflection `d n − e n`, invariance under a common added history,
  uniform reference motion under zero deflection, and the finite relative-area
  converse. No `RelativeTwoBody.lean` module or Law III theorem is present.
  No mass/force law/limit is derived.
- Order 3 (time subdivision): `Polygon/StripArea.lean` proves signed sums —
  every two-cell chord triangle has signed doubled area `h^3*det(v,a)`, equal
  for all cells, so the signed total is `k*h^3*det(v,a)`. This does not prove an
  absolute-area sum; that obligation and a geometric strip decomposition remain
  open.
- Order 7 (Proposition IV): `Comparison/CircleCompare.lean` carries the exact
  finite sagitta-chord relation as a premise and proves equal-time
  `forceBySagitta` ratios proportional to the sagittae;
  per-edition limiting routes recorded, not derived (editions kept separate).
- Dependency graphs: `scripts/plot_graphs.py` renders the module and
  passage/reference dependency graphs to `docs/graphs/*.png`; see
  `research/figures.md`.
Open: order 4 (P3 convergence — needs a Fraction Cauchy-Schwarz/triangle
inequality, which the raw `equiv` relation makes non-trivial), order 8
(Arg004-Arg006), absolute polygon-strip sums, and the limiting routes/ODE
interpretation for Props III/IV.

## 1 October 2026 merge corrections

The Proposition III moving-centre theorem now derives the original relative
conclusion through Corollary VI, Law I and Proposition II with aligned vertex
times. Absolute strip-area completion has been withdrawn; the signed identity
remains checked. The absent-module claims were removed, and SVG/PNG/PDF
figures now preserve evidence status and legends. Both Lean 4.19.0 builds and
all 245 generated reference/axiom checks pass. See
[the verification record](VERIFICATION.md#merge-corrections-verified-on-1-october-2026).
