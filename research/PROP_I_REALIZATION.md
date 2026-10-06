# Proposition I realization: premises and checked finite steps

## Historical-file migration, 6 October

The uncommitted refactor places one Newton result in each historical file,
with exact diplomatic Latin and separate witness formalizations. Elementary
support remains in BarrowLib, classical coordinate special cases in ClassicsLib,
and completed/modern motion work in ModernLib. Qualified names and theorem
statements are preserved; module paths intentionally change. See the
[migration record](HISTORICAL_FILE_REFACTOR.md#executed-migration-6-october)
and [verification](verification/historical-file-refactor-2026-10-06.md).
This changes organization, not historical proof-completion credit.

## Given-motion consistency bridge, 6 October

[The consistency checkpoint](verification/given-trajectory-consistency-2026-10-06.md)
now proves a conditional theorem for an independently supplied state curve.
Finite stability accumulates its rational samples' one-cell mechanical
residuals; a shrinking scalar local-source budget and representation of the
supplied curve then prove equality with the retained polygon limit. The
all-interval swept-fan law follows, and the actual matched-region outer
content tends to zero in a separate theorem. Neither agreement nor either
area conclusion is assumed. Local consistency is an additional explicit
premise, not part of trajectory existence. Deriving it from independently
stated motion laws, identifying ordinary swept-sector area and certifying
Newton's stage-local limiting proofs remain open. This adds no historical
completion credit and does not release force-specific applications.


## Primary proof convention, 6 October

The user now authorizes an existing trajectory as an explicit postulate.
In Lean this is the given curve parameter, with mechanical and regularity
premises stated separately. Existence is assumed in this route, not credited
as proved. The earlier trajectory constructions remain checked supporting
results; they are no longer a prerequisite for the primary historical proof.

(A) Proposition I's goal is swept sector area proportional to elapsed time,
hence equal swept areas in equal times. `SweptArea.Proportional` states the
intrinsic curve-fan version for a given trajectory, and
`GeneralForceArea.proportional_swept_area` supplies the retained constructive
instance. (B) The nonnegative area between Newton's polygon and the given
trajectory is a separate approximation control. Proving (B) tends to zero
helps justify the limiting passage; it is not the area law. Neither (A),
(B), nor convergence to the supplied trajectory belongs in the existence
postulate. Equal sector sums do not establish (B).

This is a user-authorized editorial interpretation of the proof convention,
not an explicit new axiom quoted from Newton. The Lean parameter introduces
no global `axiom`. Ordinary sector-area identification, the mechanical
polygon-to-given-curve bridge, and the invoked lemma proofs remain obligations.
See [trajectory-postulate checkpoint](verification/trajectory-postulate-2026-10-06.md).
The following construction record is retained as supporting work.

A.6 now uses regional Conditions throughout the existing construction.
The finite frame records a sample bound B on a coordinate band, the small-time
budgets r0*V<=|ell| and |x0|+T*V<=R0, and that this band lies in the oracle
region; V=|v0|+T*B. One partial-time invariant derives actual/coarse and both
shadow membership before sampling, including the first shadow kick. Endpoint,
prefix, time, polygon, region/content and secant results use these derived
certificates. No membership trace or whole-plane force premise is supplied.

SampledValues and CompletedForce now operate on values with a certified
regional representative. Representative independence is proved before choosing
that name; an equivalent arbitrary name need not stay inside the region.
GeneralForceTime.gamma_band passes both radii to the constructed curve: the
upper closed-ball bound holds, and any closed ball containing the position
has radius at least r0. These are coordinate L1 bounds, not an inverse-square
law. The harmonic instance retains its True region and old public names.
The actual Euclidean Kepler sampling instance remains within A.6, after the
general Proposition I proof, as the user clarified on 5 October evening.
GeneralForceArea now constructs swept area from fans of actual curve nodes
and proves area = |ell|*t/2 (or ell*t/2 oriented) on the existing local
regional Lipschitz curve. The actual completed between-path content now has
a grounded PolygonTrajectoryEnclosure and Vanishes instance; no enclosure or
area-limit hypothesis is supplied. BinaryLift shares the two-input completion
kit before the new area operation is built. Separate De Motu witness, 1687 and
1713 wrappers remain modern reconstructions, with planarity built into the
model. Unsigned swept area counts multiplicity; ordinary sector-union content,
unrestricted force/rate identification and the historical limiting passage
remain separate. See the [curve-area checkpoint](verification/constructed-central-area-2026-10-05.md)
and the [Latin proof route](PROP_I_REALIZATION.md#proof-dependencies-and-the-implementation-route).

`GeneralForceArea.constructed_interval_area_law` now extends that conclusion
to every pair of times in the same local domain: actual unsigned interval
fans converge to `abs(ell)*abs(t1-t0)/2`. Address independence, uniqueness,
endpoint reversal, zero-length intervals and equal areas for equal elapsed
lengths are proved; adjacent completed fans compose by addition. See the
[interval checkpoint](verification/constructed-area-intervals-2026-10-06.md).
The Laws' Corollary 1 now has a checked finite rational proof route:
`ImpulseComposition.uniform_endpoint_lines` derives both transverse endpoint
constraints without using the diagonal theorem; `Parallelogram.intersection_unique`
then proves the opposite corner. The separate 1687, 1713 and NATP00090
reconstructions follow that route. Direct impulse composition includes
parallel/opposite/zero cases and `next_arrival_diagonal` connects it to the
actual central-force recurrence. Directed additive velocity changes and
subsequent uniform motion remain explicit mechanical model premises. Only
1713 explicitly states impulses at A and cites Laws II/I in this proof;
NATP00089's composition assertion remains a hypothesis. See the
[composition checkpoint](verification/laws-corollary1-2026-10-06.md).
Lemma III Corollary 4's chord-boundary component is now proved for a given
uniformly controlled curve, including every completed point of each closed
chord and both trace directions. `constructed_uniform_curve` derives that
modulus for the actual general motion; `constructed_chord_boundary_limit`
and `constructed_polygon_boundary_limit` prove the inscribed-chord and actual
force-polygon limits separately. The source graph now traces the preceding
corollaries, with distinct De Motu witnesses and printed editions. See the
[boundary checkpoint](verification/lemma3-chord-boundaries-2026-10-06.md).
The supporting-line boundary branch now constructs finite meetings from
support inequalities, derives their endpoint rectangle, and controls every
completed point of both joined segments. With convergent finite samples of a
given uniformly controlled curve, shrinking maximum cell spans give a
proved two-sided boundary limit. Coincident lines and both coordinate
orientations are included. The 1687 and 1713 wrappers remain separate; actual
tangent identification, vertical tangent patches and the full curvilinear-area
enclosure proof remain open. See the
[supporting-boundary checkpoint](verification/lemma3-supporting-boundaries-2026-10-06.md).
The monotone-rectangle increment now derives lower/upper rectangle-set
enclosure of a fixed given graph, including all completed closure points,
and constructs the largest actual cell width. It proves the exact equal-width
rectangle-sum gap and the unequal-width bound by maximum width × total height,
then exhausts that derived gap. Endpoint aliases and zero widths are included.
This connects finite geometry to the rectangle sums; ordinary union-area
identification and the ultimate curvilinear-area ratio remain open. See the
[rectangle checkpoint](verification/lemma2-3-monotone-rectangles-2026-10-06.md).
No arclength theorem or completion-score increase is added; force-specific
applications remain held.

GeneralForceGrowth now needs Lipschitz regularity only on the computed ball.
With E=2*E0, S=|x0|+tau*|v0|, M=2*(S+tau*T*E), its radius is R=M+T*M/tau
and its force bound is B=L*R+E. CalibratedGrowth.driftCap_budget proves
|x0|+T*(|v0|+T*B)<=R directly from the existing calibrated window. This closes
the geometric budget before using regional force growth; the shared invariant
then derives every actual/coarse/shadow sample bound. Data depends on the
initial state and precision scale and only requires the oracle region to
contain that finite ball. The length cap retains positive time-unit invariance.
Singular laws use the annular Conditions constructor. No completion score or
historical proof is added by this interface repair.

TASKS.md order 4. This note identifies, stage by stage, what Proposition I
asserts, what its cited dependencies supply, and which further premises a
realization of the motion needs for a **varying** central force. Lean results
are modern rational-coordinate reconstructions (`modern_reconstruction`),
not historical proofs.

The [theorem-growth study](THEOREM_PROLIFERATION.md) separates implementation
inventory from discharged obligations. PolygonValues now shares the finite polygon alias/joining proof, and
GeneralForcePolygonCurve constructs the general whole-edge map;
the historical P1–P5 boundaries below stay unchanged.

The 4 October handoff's [foundation inventory](BARROWLIB_BOUNDARY.md) is
implemented for its minimal bootstrap. BarrowLib's generic finite triangular
maps now have actual iteration bounds, cross-map perturbation (including
sampling error E), local two-half/full-cell estimates and derived finite
mesh-uniform accumulation in the retained τ₀=1 gauge under T(1+L) ≤ 1/2. Global-contract foundation names wrap shared pointwise estimates;
the regional Newton clients certify only the actual comparisons used. [ForceClasses](GENERAL_FORCE_DESIGN.md)
constructs acceleration values, connects bounded iterates to actual Newton
schedules, and derives continuous-force local consistency from a modulus.
Harmonic and parallel fields remain instances. GeneralForceEndpoint now
constructs fixed-time endpoint Cauchy names/values from actual Lipschitz central
sample schedules, with derived geometric precision and adjacent error. Its
premises are regional force comparison, a calibrated window and a band
force bound with geometric time budgets; every actual/shadow bound is derived. Harmonic force
bounds are derived on its short family, and the resulting general value equals
the old harmonic endpoint value. GeneralForcePrefix/GeneralForceTime now
construct a continuous local binary-time state/position map with uniform prefix
convergence, address independence, initial/zero values and full-endpoint E/G
agreement. The harmonic map is an exact corollary with all its bounds derived.
Kepler sampling, restart/gluing, interior-time E/G and
precision/partition independence and unrestricted P5 remain
explicit obligations. D.2 extracts the generic completion, geometry,
binary-time and position-value layers. B.1 proves E/G agreement at every
dyadic rational time, with explicit finite numerator addresses and endpoint cases. B.2 constructs
within-cell polygon names and a mesh-explicit whole-edge bound. Both same-cell
and shared-boundary aliases agree before polygonMap is lifted to the time
quotient. Fixed-integer harmonic subdivision and its actual accumulated bound
now yield dyadic E/G agreement. TimeCalibration now proves the weighted gauge
|x|+τ₀|v|, actual finite sample-error accumulation, dimensionless growth/windows,
Cauchy-gauge equivalence and positive time-unit invariance. Harmonic and parallel
cells are instances; exact harmonic mechanics commute with unit rescaling.
C.1 now constructs the actual harmonic matched region as cell closures of
rational simultaneous connectors. Its nonnegative finite-square outer content
D_mesh has a derived 4*C²/2^m bound and decay. HarmonicPathContent constructs
its Cauchy scalar from the all-cover cut by shrinking intervals; lower-cut
identification and independence of the initial cover are proved. No scalar
area or Cauchy premise is supplied. GeneralForceSecants now derives uniform
convergence of completed bracketing dyadic position secants to constructed
velocity; HarmonicSecants applies it to the retained harmonic curve. These
are actual curve endpoints, including the final boundary, not finite polygon
secants alone. CompletedForce now constructs force values at completed
positions from the actual oracle samples, with representative independence,
Lipschitz control and precision-scale independence. Actual prefix force samples
converge uniformly to the force at the constructed curve; the retained harmonic
extension equals scaling by -w. GeneralForceAccelerationSecants now proves
uniform convergence of completed dyadic velocity secants to the force at the
constructed position, with derived bound H_m*L*(V+K) and a retained harmonic
corollary. Ordinary-area identification and unrestricted difference quotients
remain open.
GeneralForcePolygonCurve now constructs the actual quotient coarse polygon
with whole-edge error (T*V+A)/2^m and uniform convergence, including zero time
and shared initial endpoint. Six retained harmonic proofs now instantiate the
shared PolygonValues core with unchanged theorem statements; the general
harmonic polygon equals the retained map. GeneralForcePathRegion/Content now
construct the actual general closed-cell connector union and its all-cover cut
and canonical scalar, with budget 4*C²/2^m, nonnegativity, zero time and decay.
MatchedRegion shares closure/connector/cover geometry with the retained harmonic
client. Their harmonic instance has exactly the old region and scalar content,
independently of the different initial cover bounds.
QuadraticEstimates now derives the actual finite second-order position
remainder t²*(L*t*V+E) and exact t*h*|a(x0)|/2 half-mesh bias. The actual
parallel endpoint family constructs Cauchy values at every nonnegative rational
time and proves the exact quadratic state. Galilean potential and triangle
identities apply to those completed endpoints with the half coefficients; the
ratio stays motion-dependent. GeneralForceQuadraticSecants now passes the
actual finite remainders to completed central curve values. The normalized
position departure 2*(Delta_x/H-v_left)/H converges uniformly to the completed
force with error H*L*(2V+K), including the final boundary. Cauchy-name tail
boundedness proves that mesh times the actual force sample magnitude vanishes;
no extra force-bound or Taylor field is supplied. The retained harmonic curve
inherits the result. ConstructedHarmonicPotential now evaluates the harmonic polynomial potential
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
radial potential steps remain open. Those supporting quantity results receive no separate completion credit.
The foundation has no import from a Newton-specific file and no derivative,
integral or ODE primitive.

The governing target is now the **given-trajectory proof variant**. Existence
is an explicit postulate; the swept-area law is the conclusion to prove. The
area BETWEEN polygon and trajectory remains a distinct approximation control.
See [path defect](PROP_I_PATH_DEFECT.md) for stage-local premises and the
remaining geometric identification obligations. Given-curve lemmas serve
this primary route; constructive existence remains supporting work.

## What the text asserts

1687 [NATP00077 par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45)
and 1713 [NATP00082 par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51)
share the argument almost verbatim:

1. *Dividatur tempus in partes æquales*: equal time cells.
2. Law I gives the inertial continuation `Bc = AB`; Corollary 1 of the laws
   places the body at C after a single impulse at B toward S.
3. Parallels `SB ∥ cC` give equal triangles, and *componendo* the sums of
   areas are as the times.
4. *Augeatur jam numerus & minuatur latitudo triangulorum in infinitum*:
   by Lemma III Cor. 4 the ultimate perimeter is a curve, the force acts
   *indesinenter*, and the areas remain proportional to the times.

De Motu Theorem 1 (NATP00089 par9, NATP00090 par17) makes the same passage
with no numbered limiting lemma (M2.md).

## Proof dependencies and the implementation route

The following chain was checked against the **proof paragraphs** of the
archived TEI on 5 October evening, rather than inferred from the order of the
statements. [dependencies.json](dependencies.json) records each accepted edge
with its witness, passage, URL, classification and confidence. Formal references now identify the finite composition proofs on their own
edges. The remaining limiting edges are still obligations; a reference
records a reconstruction, not certification of the full historical step.

| Proof step | 1687 proof passage | 1713 proof passage | Dependency and formal obligation |
| --- | --- | --- | --- |
| Rectilinear continuation and impulse composition | [Prop. I par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45) | [Prop. I par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51) | Law I and the laws' Corollary 1 are explicit citations. The finite drift/kick construction must reproduce the inertial continuation and the radial deflection before proving equal triangles. `CentralSchedule.cell_momentum`, `det_cell_area` and `swept_eq` supply the rational planar reconstruction. |
| Why the parallelogram gives the position | [Laws Cor. 1 proof par8](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par8) | [Laws Cor. 1 proof par8](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par8) | Both proofs use unchanged transverse approach velocity and the intersection of two parallel lines. `uniform_endpoint_lines` now derives those constraints in the rational mechanical model, then `intersection_unique` derives the opposite corner. `next_arrival_diagonal` connects composition to the actual central cell. Only 1713 explicitly cites Laws II/I and initial impulses; the separate 1687 model specialization does not attribute those clauses to its text. |
| Finite composition of the areas | [Prop. I par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45) | [Prop. I par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51) | The equal-triangle argument is iterated and the areas are added. The separate edition `finite_componendo` results and `CentralSchedule.swept_eq` implement this finite step. Constant areal product alone does not implement the swept-area conclusion. |
| Curvilinear perimeter | [Lemma III Cor. 4 par10](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10) | [Lemma III Cor. 4 par11](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11) | Proposition I explicitly cites this corollary. *Et propterea* refers to the preceding rectangle/chord/tangent figures, now traced in separate source edges. The given-curve chord case has a proved two-sided closed-boundary limit with an explicit uniform modulus. The actual general force curve derives its own modulus, and its varying polygons have their own proved whole-edge boundary limit. Finite rational monotone supporting cells now have derived crossings, rectangle enclosures and two-sided whole closed boundary limits. Tangent identification and the full historical curvilinear-area enclosure inference remain open; no arclength claim is made. |
| Unequal widths reduce to the largest width | [Lemma III proof par6](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par6) | [Lemma III proof par7](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par7) | Lemma III reuses Lemma II's figures and equal limiting ratios implicitly (*Eædem rationes ultimæ*), then bounds the gap by the rectangle of maximum width. `rectangle_gap_bound` retains the integer arithmetic. The fixed-interval monotone graph reconstruction now derives completed lower/upper point-set enclosure, constructs the actual largest width and proves the rational rectangle-sum gap bound and exhaustion. Identification with ordinary geometric union area and the actual motion remains separate. |
| The enclosing rectangle becomes arbitrarily small | [Lemma II proof par4](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par4) | [Lemma II proof par5](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par5) | Lemma II identifies the gap with one width times total height and explicitly invokes Lemma I. The rational graph reconstruction now proves the exact equal-width rectangle-sum gap and its exhaustion. The actual path-content budget and grounded `polygon_trajectory_enclosure` remain separate modern square-content results. Ordinary union-area and the ultimate curvilinear-area ratio remain open. |
| Approach closer than any assigned difference gives equality | [Lemma I proof par2](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par2) | [Lemma I proof par3](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par3) | Newton assumes a final difference D and contradicts the approach hypothesis. The current rational exhaustion and quotient equality arguments justify their particular constructed limits. A general historical ultimate-ratio certificate is a separate obligation. |

De Motu keeps its own chain. [NATP00090 par17](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17)
cites its Law 1 and Lemma 1; the [Lemma 1 proof par11](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par11)
contains the marked addition *per Legem 2*. [NATP00089 par9](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par9)
has changing marginal hypothesis/lemma labels whose chronology is unresolved.
Both proofs pass to infinitely many infinitely small triangles without citing
a numbered limiting lemma. Neither witness inherits the printed Lemma III.

The active proof route is therefore: finite construction and equal triangles;
construct the general curve from those motions; derive the intervening
enclosure and exhaustion; identify actual curve-fan swept area; conclude
proportionality to time. `GeneralForceArea.constructed_area_law` packages the
last two steps for the existing local regional Lipschitz construction. Its
regularity/window premises are a **modern reconstruction**, not assumptions
read into Newton's proof. Ordinary sector-union area, unrestricted force/rate
identification and the historical limiting passage remain explicitly separate.

## Obligations and status

| Obligation | Status |
| --- | --- |
| P1 finite area law | **Checked in the rational planar model, generalized**: `CentralSchedule.swept_eq` holds for any central field and arbitrary *unequal* rational cells. Newton uses equal cells. |
| P2 refinement family | **Exact finite identities**: for any field, splitting a cell `h+k` moves the endpoint by exactly `h*k*a(y)` (`refine_position`). The velocity changes by `h*(a y − a X) + k*(a z − a X)` (`refine_velocity`). The harmonic example proves both changes are nonzero while swept areas agree. The refined polygons are different polygons. |
| P3 trajectory existence and identification | **Existence postulated in the primary route, 6 October; identification remains to prove.** Supply a trajectory map, its separately stated mechanical laws and any required regularity. Do not assume that Newton's polygons converge to it or that either area conclusion holds. The verified `GeneralForceEndpoint`/`Prefix`/`Time` construction remains supporting work, including its regional assumptions and open gluing/partition questions. |
| P4(A) swept-area law, the Proposition I conclusion | **Constructed-curve and conditional given-motion fan laws checked; historical given-trajectory proof open.** `SweptArea.Proportional` states the all-interval fan-area target, with the curve provided as data. `GeneralForceArea.proportional_swept_area` derives the retained regional instance from the checked interval law. The actual curve-node fans give `abs(ell)*abs(t1-t0)/2`; existence of the fan limit is part of the conclusion. Unsigned fans count multiplicity. Ordinary sector-union identification and the historical limiting passage remain open. No area law is assumed in the trajectory postulate. |
| P4(B) between-path approximation control | **Retained constructed-curve content control checked; bridge to an independently given mechanical trajectory open.** `GeneralForcePathContent.polygon_trajectory_enclosure` and `polygon_trajectory_defect_vanishes` ground actual matched-region all-cover content with bound `4*C²/2^m`. Initial endpoints agree and the final connector is retained. This set counts overlaps once and is distinct from swept fan area. Its convergence is not part of trajectory existence, and equal swept sums alone do not prove it. |
| P5 force identification | **Constructed dyadic rate bridges checked.** `GeneralForceSecants` identifies completed bracketing position secants with constructed velocity; `GeneralForceAccelerationSecants` identifies completed bracketing velocity secants with force at the constructed position, uniformly including the final boundary. `CompletedForce` operates on the certified regional completion domain and is independent of force precision. Restarted finite remainders and exhaustion derive the estimates; harmonic results are corollaries. Unrestricted difference quotients, motion-precision/partition independence and historical justification of continuously acting force remain open. |

## Regularity questions retained separately from existence

Proposition I cites no premise on the force's regularity. The nearest
same-stage qualification is in Lemma X, which Proposition I does not cite:

- 1687 [par27](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par27):
  *urgente quacunque vi regulari*.
- 1713 [par28](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par28):
  *urgente quacunque Vi finita … sive Vis illa determinata & immutabilis sit,
  sive eadem continuo augetur vel continuo diminuatur*.

Importing this qualification into Proposition I would be an
`editorial_interpretation` and needs its own justification. The 1713 form is
the more usable one. A finite force that is monotone along a path segment has
bounded variation there, so the velocity change in P2 telescopes like the
Lemma III width argument already checked in `rectangle_gap_bound` (M2). The
force is a vector, however. Monotone magnitude leaves the change of
direction to control, which needs the radius bounded away from S
(compare the vertex-at-S counterexample in `Converse.lean`).

Any such regularity premise brings a scale. A Lipschitz bound `L` on the
force defines a local dynamical time `1/√L`; the finite consistency estimates
require the cell small compared with the relevant local scales. Newton's clauses assert finiteness
without a value: they fix the existence of a scale, and its size depends on
the law and the region. The retained harmonic bounds use τ₀=1. The new
calibrated finite estimates use `|x|+τ₀|v|` and the dimensionless window
`n|h|(1/τ₀+τ₀L) ≤ 1/2`, with proved positive time-unit invariance; see [scales and units](GENERAL_FORCE_DESIGN.md#scales-and-units).

## Converse side

`CentralSchedule.unequal_cells_converse` extends the finite Proposition II step
to unequal cells. If two consecutive doubled areas are proportional to their
nonzero durations, the impulse at the shared vertex is parallel to its radius.
Proposition II's statement speaks of areas proportional to times, so this is
the finite content it needs when cells are unequal.

## Next bounded step

The next primary step is to derive the new local consistency premises from
independently stated mechanical laws and regularity of the given motion.
The conditional identification, all-interval fan law and separate matched-region
content decay now compile; they do not derive those consistency premises. Trace
Newton's finite impulse and limiting arguments against that curve; derive
the between-path control separately, without hiding curve/polygon agreement
in the existence postulate. In the invoked Lemmas II–III chain, the remaining
area bridge identifies rectangle side-product sums with their geometric
unions and the enclosed curvilinear area, then proves the ultimate ratio
with its nonzero-area premise. This supporting bridge is not Proposition I's
conclusion and is no longer a reason to restart trajectory construction.
Ordered finite partitions now derive their actual point-set
coverage and completed enclosure; their maximum width, exact equal-width
sum gap, unequal-width bound and exhaustion are proved. The supporting-line
branch also has derived crossings and whole closed boundary limits with
explicit finite data. Actual tangent identification and vertical patches
remain separate. The actual constructed force polygons already have their
own derived two-sided limit. Scalar area, trace convergence and arclength
remain distinct. Force-specific applications follow the general proof.

The harmonic field now has derived mesh-uniform actual state and endpoint-error
bounds, a proved square enclosure and nonnegative cover budget for matched
polygonal patches, and constructed fixed-rational-time endpoint Cauchy names;
see [harmonic refinement](HARMONIC_REFINEMENT.md). Uniform variation with
rational time is now derived in HarmonicTimeComparison, with an explicit
positive tolerance controlling every approximant. HarmonicBinaryPrefix now
constructs Cauchy names from actual intermediate-time prefixes of one global
polygon family. CauchyValues now realizes them in an explicit quotient and
proves representative-invariant time/tail bounds. BinaryTime and
HarmonicTimeRealization now construct the time quotient and continuous state
map, including endpoint/alias identities. PositionValues now derives the planar
position map, completed coordinate squares and positive position separation.
Addresswise same-time coarse polygon names and uniform whole-edge distance
control are now proved in HarmonicPolygonCurve. Both kinds of alias independence
construct polygonMap on the same time quotient. HarmonicPathRegion now
constructs the closed matched region, its all-cover infimum lower cut and a
derived vanishing square enclosure. See TRAJECTORY_DEFECT_REGION.md.
Cauchy scalar realization and cover independence are now proved in
HarmonicPathContent. Ordinary sector-union area identification, P5 and partition
independence remain distinct. CompletedForce now proves representative compatibility for regional Lipschitz
sampled force data on the certified completion domain; finite centrality alone
does not supply it. gamma_band proves the constructed curve's closed radial
bounds. The proper annular harmonic control tests that interface; the actual
Euclidean Kepler oracle remains required by A.6. P3's existence is postulated in the primary route; identifying Newton's
polygons with that given trajectory remains open. P4 now has the intrinsic local curve-fan area law; ordinary sector-union
identification and Newton's historical limiting passage remain open.
The [construction ledger](CAUCHY_REALIZATION.md) records the checked quotient
and time-domain steps and the remaining geometric obligations.

For a general varying field, any force-difference premise must be explicit and
named: a Lipschitz-type bound is a modern repair; the 1713 monotone-finite
qualification on a radial segment is an editorial candidate and does not alone
control a force vector's change of direction. No ODE theorem is imported.
