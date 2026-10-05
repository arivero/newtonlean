# Active proof obligations

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

This queue implements [the approved goals](GOALS.md). A checked finite
diagnostic is not completion of the corresponding historical proposition.

**Priority (3 October user instruction): Proposition I, then II, III, IV,
in De Motu, 1687 and 1713 separately.** The primary forward variant constructs
the trajectory. Its main polygon–trajectory area is distinct from the Kepler
area; supplied-curve enclosures are diagnostics. See PROP_I_PATH_DEFECT.md.

Earlier priority case: zero force and rectilinear motion.
ZeroForce.lean now derives the inertial map, unchanged velocity, exact
cross-denominator subdivision agreement, restart, rest and within-cell
positions from the constructed recurrence. Its zero-area timing example uses
different initial velocities, not nonuniqueness for fixed data. See ZERO_FORCE.md.
InertialControl.lean now supplies an explicit positive time radius controlling
both coordinates of inertial displacement, uniformly in rational base time,
including actual zero-force cells. InertialDefect.lean proves signed finite
defect cancellation for arbitrary closed inertial walks. Next make the extension
beyond rational times precise before claiming a complete inertial case.
Then continue the nonzero-force within-cell extension below.

Current progress: the bounded source map (1) is recorded in SECTION_II.md,
with unresolved De Motu counterparts explicitly retained. The equal-cell
finite recurrence now satisfies restart and contact (2), including the
constructed lattice velocity-jump law. A one-cell closed strip between
spatially compatible coarse/fine polygons is now exact finite triangle
algebra. The bounded rational common-force/time comparison (3) now derives
an endpoint mismatch `h*k*a` under an explicit end-kick convention, with equal
terminal velocities. Thus general refinement must allow controlled non-nested
endpoints; compatibility is not assumed. See TIME_SUBDIVISION.md. No
continuous-time realization is inferred. Finite arbitrary-partition formulas
and the exact residual/mesh coefficient bound now follow from the actual
end-kick recurrence in PartitionControl.lean; see PARTITION_CONTROL.md.

| Order | Obligation | Acceptance criterion |
| --- | --- | --- |
| 1 | Stage-local I–IV source map | Exact passages and supported dependencies for 1687/1713; De Motu counterparts qualified witness by witness |
| 2 | Finite contact and restart | Contact of actual recursively constructed cells, with any velocity jump derived from the displayed impulse; restart from the matching state |
| 3 | Time subdivision | Constant-force rational-time part closed: two-cell mismatch; endpoint and within-cell residual/mesh bounds (PartitionControl, PartialCell); an explicit small-residual refinement per tolerance (UniformRefinement); exact position/velocity comparison and packaged gap `partition_gap` for arbitrary partitions at a common rational time (PartitionComparison). Signed two-cell triangle sums checked (`StripArea.lean`): each triangle has signed doubled area `h^3*det(v,a)` and the signed total is `k*h^3*det(v,a)`. The value may be negative. Still open: absolute polygon-strip defect sums and their geometric decomposition, extension beyond rational times, varying force |
| 4 | Proposition I realization | Obligations P1–P5 are isolated in PROP_I_REALIZATION.md. Finite area/refinement identities, actual harmonic schedule bounds and matched-patch square covers are checked; see HARMONIC_REFINEMENT.md. Actual prefixes of one global dyadic family now construct Cauchy names and quotient values. Under T≥0 and T*(1+abs(w))≤1/2, BinaryTime and HarmonicTimeRealization derive time names, the proved time quotient, same-grid state control by 2*(1+abs(w))*M times actual time difference, and a continuous state map with endpoint/alias identities and zero cases. See CAUCHY_REALIZATION.md. PositionValues now derives planar values, gammaPosition, completed coordinate squares and positive sample position separation. HarmonicPolygonCurve now constructs the same-time coarse polygonMap with whole-edge bounds and both alias cases. HarmonicDyadicAgreement identifies independently rescaled values at every dyadic rational time. Explicit positive time calibration has actual finite bounds and proved Cauchy/unit invariance. Whole-plane sampled Lipschitz forces now have constructed fixed-time endpoints and a continuous local binary-time state/position map; GeneralForceGrowth derives their actual/coarse/shadow sample bounds from force data and the initial state. Removing global_region and deriving confinement, with the Kepler instance, is required by A.6. Uniform prefix convergence, address independence and full-endpoint E/G agreement are derived; the harmonic map is an exact instance. Local confinement, gluing, general interior-time E/G agreement and external real-time identification remain separate. HarmonicPathRegion now defines the actual closed matched region and D_mesh as the lower cut of all finite square-cover budgets, with a derived 4*C²/2^m bound and decay. HarmonicPathContent now realizes the all-cover cut as a Cauchy scalar, independently of the chosen initial cover; scalar nonnegativity, budget control, zero time and decay are proved. Initial endpoints agree, the final connector is explicit, and reversed connectors count the same points. GeneralForceSecants now proves uniform convergence of completed bracketing dyadic position secants to constructed velocity, including the right boundary; HarmonicSecants derives the harmonic corollary. CompletedForce now extends the sampled force to completed positions with precision independence and uniform convergence of actual prefix force samples; its harmonic extension equals scaling by -w. GeneralForceAccelerationSecants now proves uniform convergence of completed dyadic velocity secants to that constructed force, with the retained harmonic corollary and rounding error explicitly exhausted. GeneralForcePolygonCurve now constructs the actual quotient polygon with uniform whole-edge bound (T*V+A)/2^m, sharing alias/joining proofs with the retained harmonic map and preserving all statements. GeneralForcePathRegion/Content now construct the actual general closed matched region and its all-cover cut and canonical Cauchy scalar, with nonnegativity, bound 4*C²/2^m, zero time, decay and initial-cover independence. MatchedRegion shares cell/connector/closure geometry with the harmonic client; the general harmonic region and content equal the retained objects exactly. Other time parameters, arbitrary partition independence, ordinary-area identification and unrestricted difference quotients remain separate. GeneralForceQuadraticSecants now derives uniform normalized second-order position departure toward the completed force, with H*L*(2V+K) error, using the same completed secant operators; no Taylor premise is supplied. ConstructedHarmonicPotential now constructs polynomial potential values and derives uniform dyadic Delta V/H² convergence to -mass*dot(a_left,a_left)/2 on the retained constructed harmonic curve, with an O(H) error and no supplied potential asymptotic. GeneralForceTangentTriangle constructs the actual signed doubled tangent triangle and derives uniform triangle/H³ convergence to det(v_left,a_left)/2, with H*L*V² error. General radial potentials and the D_mesh relation remain open. A supplied curve or scalar budget does not complete the primary target |
| 5 | Proposition II converse | Finite Case-1 step checked (Converse.lean): equal oriented areas ⇔ deflection cC parallel to SB; rational central kick when B≠S; counterexamples for unsigned areas, vertex at S, and the undetermined sense. Case 2 finite step (uniformly moving centre) and the unequal-cell converse (CentralSchedule.lean) also checked. Next: the vanishing-triangle passage with a justified realized curve, keeping direction and sense distinct |
| 6 | Proposition III relative motion | Finite integer-polygon step checked in `RelativeMotion.lean`: Corollary VI, Law I, relative deflection `d n − e n`, and relative-area converse. `propIII_via_moving_centre` explicitly cancels the reference history in both bodies, identifies the correctly timed uniform reference vertices, and applies Proposition II to the original relative-area hypothesis. No Law III, mass, force law or limit is derived. Open: the limiting passage from a realized relative orbit and any force/mass/time-scale interpretation |
| 7 | Proposition IV circular comparison | Closed **finite core** (`Comparison/CircleCompare.lean`): the exact intersecting-chords relation `s*(2r-s)=(c/2)^2` carried by a `CircleChord`, and equal-time `forceBySagitta` forces proportional to the sagittae (`force_ratio_is_sagitta_ratio`). The per-edition routes (1687 Prop II+Lemma V+Lemma XI; 1713 Prop II+Prop I Cor 2&4+Lemma VII) are the limiting steps that turn this into `arc^2/r`; they are documented as separate editorial interpretations, not derived, so the editions stay apart. Open: the limiting route itself and the force interpretation |
| 8 | Boundary/action diagnostic (arguments in `action-arguments/`; Arg004–Arg006 support action as the kind, location and scale of a constant, with no value fixed) | Open. Arg004 (Cavalieri strip, planar symplectic), Arg005 (rational-cell MonotoneEnclosure + identify `tri` with PartitionControl's cross statistic), Arg006 (discrete curvature radius vs `p^2/(m*|F_perp|)`) are specified but not yet formalized. Do not assume a universal constant |

For obligations 4–7, report a proved special case separately from the whole
proposition. If a historical premise cannot be recovered, continue independent
obligations while retaining that gap. A source-map entry is not a Lean theorem.

Order 4, current handoff: D.1 and the minimal foundation bootstrap are
recorded. The user-requested [theorem-growth study](THEOREM_PROLIFERATION.md)
and one explicitly requested sequential Astra review recommend the next bounded
unit: a shared finite-vertex polygon core and actual general whole-edge map.
This is now implemented, with six old harmonic proofs using the core and
unchanged statements, uniform error (T*V+A)/2^m and exact harmonic specialization.
MatchedRegion now shares the actual general matched-region geometry with the
harmonic client. GeneralForcePathRegion/Content construct the all-cover cut and
scalar with geometric decay; their harmonic instance equals the old region and
content. Existing APIs and explicit sample bounds remain; raw counts receive
no completion credit.
Task A has a [sampling interface](GENERAL_FORCE_DESIGN.md),
constructed acceleration values, actual bounded polygon iterates and finite
mesh-uniform refinement accumulation. GeneralForceEndpoint now derives
fixed-time Cauchy names/values for globally compared Lipschitz central samples,
using geometric precision selection and bounded actual/shadow force arrivals.
"Globally compared" is the whole-plane premise `global_region`; it excludes
the laws singular at the centre, so order 4 is not advanced for Newton's
target laws until region confinement replaces it (handoff Task A.6), and the
curve's own area law remains unstated (handoff Task E).
Its harmonic instance derives the required sample bounds and equals the old
endpoint construction. GeneralForceTime now constructs the continuous local
binary-time map, including uniform prefix convergence, address independence and
full-endpoint E/G agreement; its harmonic instance equals the old map. Continuous
class (b) has local consistency through its own modulus; non-Lipschitz motion
existence/uniqueness, local-annulus stability, gluing and general interior-time
E/G agreement remain separate.
D.2 extracts the remaining generic completion/geometry/time layers into the
foundation. B.1 now closes E/G agreement at every dyadic rational time, with
explicit numerator addresses and actual integer-subdivision accumulation. B.2 constructs within-cell
polygon names, a uniform whole-edge bound and a quotient polygonMap after
proving same-cell and shared-boundary alias independence, including zero time.
TimeCalibration now proves weighted actual finite bounds, dimensionless windows,
Cauchy-gauge equivalence and positive time-unit invariance, with harmonic and
parallel instances. C.1 now has actual harmonic and general Lipschitz matched
regions and finite-square outer content, defined by all-cover cuts and canonical
Cauchy scalars. Shared one-square-per-cell containment gives geometric decay.
General radial potentials and their curved steps,
restart/gluing, derived confinement, ordinary-area/Kepler-area identification and
P5 unrestricted-rate remains an obligation. The first P5 bridge now
identifies constructed velocity as the uniform limit of completed dyadic
position secants, using derived finite restarted-run remainders. Its harmonic
instance uses the retained curve. C.2 now has constructed dyadic kinematic
and harmonic potential asymptotics; general radial potential construction and
unrestricted-rate estimates remain separate.
CompletedForce now supplies the force at completed positions through a proved
diagonal sample construction, with Lipschitz, rational-agreement and force
precision-independence results. Actual polygon force samples converge uniformly
to that force along the constructed curve, including the retained harmonic
specialization. GeneralForceAccelerationSecants now identifies the uniform completed dyadic
velocity-secant limit with that force, with error H_m*L*(V+K) and a retained
harmonic corollary. Unrestricted differentiation remains open.
Task C.2's finite quadratic comparison now has a derived remainder
t²*(L*t*V+E) plus the exact half-mesh bias t*h*|a(x0)|/2. A two-cell
parallel control rejects finite equality with the t²/2 predictor.
ParallelQuadraticEndpoint constructs actual Cauchy endpoint values for every
nonnegative rational time with the exact quadratic state. The Galilean triangle
and potential relations apply to those completed endpoints; both acquire a
half while their motion-dependent time ratio remains unchanged. See
[Arg007](action-arguments/261004gpt6.1solv1Arg007.md) and the
[quadratic checkpoint](verification/quadratic-finite-parallel-endpoints-2026-10-05.md).
GeneralForceQuadraticSecants now derives the normalized half-coefficient
position-departure criterion on the actual general curve. Completed secant
composition, actual finite remainders and force-name Cauchy boundedness remove
the half-mesh bias and sampling error. Its uniform target-force bound is
H*L*(2V+K), including the final boundary; the retained harmonic curve is a
corollary. ConstructedHarmonicPotential now evaluates the harmonic polynomial potential
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
radial potential steps remain open. Completion scores stay unchanged.
See the [potential checkpoint](verification/constructed-harmonic-potential-2026-10-05.md).
The binary-time parallel map remains open.

Validation is sequential and delegated. The final verification agent runs both
build targets and source/reference checks after implementation agents finish.
Use the formal-result ledger for actual theorem premises and the research state
for current completion boundaries. No task is marked complete solely because
a structure contains a field asserting its desired conclusion.
