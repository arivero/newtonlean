# General central force design and proof specification

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
The actual Euclidean Kepler sampling instance still remains within A.6 and
comes next. Task E and new completed quantities have not started. See the
[regional construction checkpoint](verification/regional-construction-2026-10-05.md).

Task A of the 4 October handoff, Sol 6.1. This design is fixed before the
estimates are implemented. Its mathematical layer is `modern_reconstruction`;
it adds no historical edge and imports no limiting theorem into Newton's text.

Use rational vector samples `sample n : Point → Point`, with a named region
`R : Point → Prop` and explicit uniform errors `e_n`. A law is represented by
samples that are Cauchy uniformly on R, not by a rational-valued assertion
that the exact acceleration is rational. Require each finite sample to be
central and inward (a nonnegative rational multiple of the negative radius).
The centre is translated to the origin. The separate parallel-force instance
has no finite centre. The Cauchy quotient later realizes the sampled values;
no limit point is a field of this interface.

This admits irrational magnitudes: for a distance-only law, approximate its
radial scalar coefficient at the squared rational radius. On an annulus
`r₀ ≤ r ≤ R₀`, coefficient error ≤ `e_n/(R₀+1)` gives vector error ≤ `e_n`.
The numerical approximation procedure and its uniform error proof are data of
the law. Neither a square root at a rational point nor an exactly rational
force value is required. The interface also admits continuous
direction-dependent coefficients. Singular laws require an explicit region
and confinement; energy confinement is not assumed proved.

Regularity is a separate contract. For class (a), and for the Lipschitz
subclass of (b), use `|sample n(p)-sample n(q)| ≤ L|p-q|+2e_n`.
Rounding samples need not themselves be Lipschitz. For continuous class (b)
or (c), use an explicit uniform modulus on the confined region with the same
additive sampling error. A modulus of continuity is not a Lipschitz constant.
Class (d) retains finite centrality without a continuity/convergence claim.
Conservative and distance-only qualifications are additional predicates;
they do not participate in the finite perturbation estimate.

Foundation estimates quantify over arbitrary rational point maps and explicit
bounds; Newton-side instances restrict those maps to inward central fields
or the permitted uniform parallel field. The abstract triangular map is

    y = x + h v,    (x,v) ↦ (y, v + h a(y)).

This is finite arithmetic, with no force, derivative or ODE primitive in
BarrowLib. A Newton schedule instantiates this map. Its estimates keep the
position and velocity error terms visible before combining the calibrated
L1 state magnitude. New shared arithmetic and tail lemmas go in BarrowLib;
old public harmonic names remain available as instances or compatibility
facades. D.2 now extracts the remaining geometry/completion/time layers and
shares coefficient-parameter tail estimates; force instances stay Newton-side.

## Scales and units

A Lipschitz contract introduces a scale. `L` has units of 1/time² and defines
the local dynamical time `τ_L = 1/√L`: `1/ω` for the harmonic field, about
`√(r³/GM)` for gravity near radius r. The latter shrinks to zero at the
centre, which is why singular laws need a confining region. A mesh converges
once `h ≪ τ_L`. The contract assumes only that a finite `L` exists on the
region; its value depends on the law and the region, rescales with the unit
of time, and fixes no universal constant. A modulus of continuity for classes
(b) and (c) carries the same kind of scale without a single constant.

The retained harmonic and finite refinement estimates use the numerical gauge
τ₀=1. TimeCalibration now carries a positive rational τ₀ explicitly:

    norm_τ(x,v) = |x|+τ₀|v|,
    K_τ(h,L) = (1+|h|/τ₀)(1+τ₀|h|L)
             = 1+|h|(1/τ₀+τ₀L)+h²L.

For n actual cells, the derived dimensionless window
`n|h|(1/τ₀+τ₀L) ≤ 1/2` gives `K_τ^n ≤ 2`. Cross-map sampling discrepancy E
accumulates to at most `2nτ₀|h|E`. The old τ₀=1 product bound and the calibrated
bound share one finite two-factor proof. Fixed positive calibration changes
neither the Cauchy condition nor its completed equivalence class for the
same coordinate family. Under a time-unit change c>0, use

    h→ch, τ₀→cτ₀, v→v/c, L→L/c², E→E/c².

Weighted norms/distances, dimensionless factors/windows and sampling budgets
are proved invariant. Exact harmonic cell mechanics commute with the same
rescaling. Lean controls detect the change in the unweighted state norm if
the calibration is omitted. These are finite estimates and Cauchy-gauge facts;
the general local binary-time map is now constructed under the named global
comparison and actual sample bounds; restart/gluing remains open.

τ₀ is a free calibration, not a dynamical necessity or an action constant.
Newton's counterpart is qualitative finiteness (1713 Lemma X *Vi finita*,
Lemma XI *curvaturam finitam*), with no numerical value. Arg006 reads it as a
local scale; no scale created by τ₀ is assigned to the motion itself.

## First estimate specification

May assume: Fraction order/arithmetic, point triangle/scaling inequalities,
explicit region membership, bounded sampled acceleration B, the displayed
Lipschitz/modulus contract and a bound E comparing two sample maps.
Must not assume: convergence of polygon families, a curve, partition
independence, P5, a potential or a nonzero action constant.

Prove one-map growth, two-map perturbation and coarse/two-half-cell mismatch
for the actual triangular map. Include additive `|h|E` in velocity/state
perturbation and retain the displacement of the sampled arrival point.
Derive finite accumulation from the actual recurrence before claiming a
mesh-uniform or Cauchy result. A supplied adjacent-error field alone is not
a derived estimate for a mechanical family.

Arithmetic pins (Lean exact rationals): harmonic `w=1`, `h=1/8`,
`s=((1,0),(0,1))`; parallel acceleration `(0,-1)` with `h=1/2`; unequal
sample maps `(0,-1)` and `(0,-2)` from the same initial state. Omitting the
`|h|E` term must fail the latter case. Zero L, zero h and zero initial state
must be covered. Unrestricted large-time amplification must not be called
a small-window estimate. Counterexamples may refute an overstrong claim;
compiler rejection alone is never an obstruction.

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

GeneralForcePrecision now chooses a monotone precision q_j with
`e_(q_j)<E0/2^j` from the proved error-vanishing contract. E0>0 is an explicit
acceleration precision scale. GeneralForceEndpoint constructs fixed-time names
from actual level-j central schedules at q_j. Regional approximate
Lipschitz comparison, the calibrated window, a band force bound B and the
frame's geometric budgets derive all comparison arrivals and coarse speed
`V=|v0|+TB`. The weighted adjacent bound is

    T*h*C + 7*τ₀*T*E,  h=T/2^(j+1), E=3*e_(q_j),
    C=B+τ₀*L*(V+TB).

Equivalent duration values require a separate actual sample-error comparison;
rounded maps need not agree at equal-valued point representations. The checked
control in EquivalentDuration detects omission of this term. Hence the derived
geometric coefficient is `T²*C+42*τ₀*T*E0`. Shared geometric tails then construct
the motion name and value, without a supplied adjacent/Cauchy motion estimate.
Zero time is included. HarmonicGeneralEndpoint derives its actual/shadow B on
the short family and proves that these general names/values equal the retained
harmonic endpoint construction. It does not assert a global harmonic force
bound. The construction now supplies confined-annulus comparison. Kepler
sampling, restart/gluing and unrestricted P5 remain separate.

GeneralForcePrefix inherits the same conditions and derived bounds at actual
represented-grid arrivals. Paired refinement holds at every prefix with the same full-window
budget. The optional next cell has weighted distance at most
`h*(V+τ₀B)`, so the adjacent prefix coefficient is
`T²*C+42*τ₀*T*E0+T*(V+τ₀B)`. The shared geometric-tail proof constructs
its Cauchy name. Same-grid increments give a calibrated time-distance bound
`(V+τ₀B)*|t-u|`; ordinary distance uses the explicit factor `1+1/τ₀`.
GeneralForceTime proves address independence before lifting the local
state/position map to BinaryTime, along with uniform prefix convergence,
continuity, initial/zero values and full-endpoint E/G agreement.
HarmonicGeneralTime derives the additional actual-grid force bounds and equals
the retained harmonic maps. General interior-time E/G, arbitrary-partition or
precision-choice independence and identification
with an external real-time interval remain separate.

GeneralForceSecants now transfers finite drift remainders to completed curve
secants. Bounded actual acceleration gives velocity change at most t*B and
position remainder from inertial continuation at most t²*B; neither finite
estimate uses regularity or a supplied rate. SecantValues proves Cauchy and
representative invariance before defining rationally divided completed position
differences and velocity projections. DyadicNodes derives the actual node times.
On the constructed general local map, each completed dyadic cell secant differs
from the left-node velocity by at most H_m*B. Time continuity adds H_m*K against
the target velocity, so these bracketing secants converge uniformly over every
binary address, including the right boundary. The retained harmonic result is
a corollary. This is the first constructed P5 rate bridge; unrestricted
difference quotients remain open; the acceleration secant bridge is now proved below.

CompletedForce now extends the same actual sampled force to the completed
position plane. SampledValues derives a diagonal Cauchy name from ordered
sample comparisons and vanishing error, proves name-equivalence transport and
then lifts the value. CompletedForce derives these comparisons with coefficient
L and additive 3*e(q_j); samples need not individually be exactly Lipschitz.
The completed extension is Lipschitz, agrees with accelerationValue at rational
points and is independent of E0 and the valid Lipschitz bound. It depends only
on the position and has zero velocity slots. No assumption q_j>=j is used;
zero-error precisions may remain constant. Actual prefix force samples have
closed error (A*L+3*E0)/2^j against the force at the constructed gammaValue,
uniformly over addresses. The harmonic extension equals scaling by -w and
applies to the retained curve. GeneralForceAccelerationSecants now derives
completed dyadic velocity secants from actual finite remainders. The finite
quotient error is L*H_m*V+3e(q_(m+j)); rounding-error exhaustion leaves L*H_m*V
at the left node. Force continuity gives H_m*L*(V+K) against the target time,
uniformly over addresses and including the final boundary. SampledValues proves
precision-offset invariance first, so the target force is the same extension.
The retained harmonic result is a corollary. Unrestricted differentiation,
motion precision independence and region-local confinement remain separate.

GeneralForcePolygonCurve now constructs the actual coarse polygon on the same
BinaryTime quotient as gammaPosition. PolygonValues derives same-cell, adjacent
and zero-window aliases from shared-position joins; harmonic and general
vertices both instantiate it. Whole-edge error is (T*V+A)/2^m, uniformly over
time, and initial endpoints agree. Six retained harmonic proofs now use that
core, and the general harmonic polygon equals the old map. This shares proof
implementation while preserving public statements. MatchedRegion now shares
closed-cell connector and cover geometry with the retained harmonic client.
GeneralForcePathRegion/Content define the actual general region and all-cover
cut and construct its canonical Cauchy scalar. The actual vertex and prefix
bounds derive a square radius C/2^m and budget 4*C²/2^m, C=T*V+A. The final
connector is included, overlaps count once in the unsigned set, and content is
nonnegative, cover-independent and tends to zero, including zero time. Exact
harmonic region and scalar equality holds despite different covering bounds.
This is the finite-square outer-content candidate; ordinary area, constructed
Kepler-area transfer and general curved potential steps remain separate.

QuadraticEstimates now derives the actual finite second-order position
comparison. Its constant-map coefficient is t*(t-h)/2; the variable-map
remainder is t²*(L*t*V+E), with explicit half-mesh distance
t*h*|a(x0)|/2 from the t²/2 predictor. ParallelQuadraticEndpoint uses this
exact finite error to construct endpoint Cauchy values at every nonnegative
rational time and identifies their full quadratic state. This is the permitted
centre-at-infinity instance, not a general central curve or external real-time
map. Its actual Galilean endpoint has potential drop -m*g²*t²/2 and doubled
tangent-deflection area t³*det(v,a)/2, preserving the same motion-dependent
time ratio. GeneralForceQuadraticSecants now derives the half-coefficient
position departure on the actual completed central curve. QuadraticSecants
composes the existing completed operators; its finite normalized error is
2*(L*t*V+E)+(h/t)*|a(x0)|. The actual shifted force name is Cauchy, so a
proved tail bound makes its sample magnitude times 1/2^j vanish. Together
with force-error exhaustion and precision-offset invariance this leaves
2*L*H*V against the left-node force. Force/time continuity gives the uniform
H*L*(2V+K) target bound, including the final boundary. HarmonicQuadraticSecants
gives the retained-curve corollary. ConstructedHarmonicPotential now evaluates the harmonic polynomial potential
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

For merely continuous fields, existence (possibly by a subsequence),
full-sequence convergence and uniqueness are separate obligations. They will
not be replaced by a structure field asserting the desired trajectory.

## Actual finite accumulation and continuous consistency

`BoundedIteration.run` constructs the actual triangular iterates. Under bounded
arrival samples, velocity is at most `|v₀|+TB`, and position is at most
`|x₀|+T|v₀|+T²B`, uniformly over meshes with elapsed time at most T.
`ForceClasses.run_eq_schedule` and the `sampled_polygon_*_bound` theorems
identify these with the mechanical schedules. `BoundedOn` and membership of
every arrival in the region are explicit premises. They apply to bounded
continuous (b)/(c), and even bounded (d), without deriving convergence.

`FiniteAccumulation` constructs actual full-cell and two-half-cell iterates
and derives their finite error recurrence. On `T=2nh`, `T(1+L) ≤ 1/2`, its
finite product bound gives `D_n ≤ 2n S`, where S includes both the actual
local defect and propagated additive sample error. B bounds first-half samples
and V coarse velocities only for `k<n`. The global comparison contract also
covers comparison locations that are not vertices of the coarse polygon;
a region-local replacement must prove those locations confined. See the
[accumulation verification](verification/general-accumulation-2026-10-04.md).
The cross-map theorem compares different fine and coarse rational samples;
`sampled_uniform_refinement` instantiates it at precisions j+1 and j with
the derived discrepancy `3e_j`, under its explicit global-region premise.

`sample_point_error` transfers oracle coherence to point distance, and
`samples_comparison_contract` derives a cross-precision global force contract
with discrepancy `3e_i` for `i≤j` when the declared region contains every
rational point. It does not treat rounded sample maps as exactly Lipschitz.
For a confined annulus, only the local version of this contract applies.

`continuous_local_refinement` derives, for each positive eps, a positive delta
and precision N from `ContinuousOn`. If the three actual sample locations lie
in the region and their drift/refinement separations are below delta, the
local state defect is bounded by `|h²|B+|h|(eps+eps)`. No Lipschitz coefficient
is substituted for continuity. This controls the local source; a stability
or subsequence construction and uniqueness require separate arguments.

The finite Frame uses an acceleration bound on the certified band inside the
oracle region. This distinction preserves the harmonic oracle's region=True:
its force is bounded on each finite ball, despite being unbounded on the whole
plane. For a singular law, the band is a genuine annulus. The zero-speed
countermodel proves why the positive-speed clause is necessary for a nonzero
inner radius. These are finite L1 radii; they are not Euclidean Kepler radii.
