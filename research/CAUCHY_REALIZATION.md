# Constructing motion from sampled central polygon families

This records the checked Cauchy-name, value and binary-time constructions and
the remaining geometric and mechanical steps for Proposition I's construction
variant. It is not a completed trajectory theorem. The mathematical layer is a modern
reconstruction with explicit rational coordinates and a chosen L1 state
gauge. The retained harmonic formulas use τ₀=1; TimeCalibration now proves
that any fixed positive rational calibration |x|+τ₀|v| has the same Cauchy
condition. Weighted finite bounds and their dimensionless windows are invariant
under a positive change of time unit. No historical dependency or supplied
curve is added.
The stage-local obligations remain in [the realization ledger](PROP_I_REALIZATION.md).

The [theorem-growth study](THEOREM_PROLIFERATION.md) recommends one shared
finite-vertex polygon implementation for the next general whole-edge map.
Completion, alias and interface counts are not separate motion-existence
milestones; the construction and remaining identifications below stay explicit.

The [foundation inventory](BARROWLIB_BOUNDARY.md) is now in BarrowLib:
generic point/triangle/convex geometry, state distances, Cauchy names and
quotient values, binary time, planar projections and coordinate squares.
The old namespaces and imports remain compatibility interfaces. Harmonic
schedule constructions, coefficients and gamma maps stay Newton-side.
The coefficient-parameter geometric-tail argument is shared without
identifying its distinct endpoint/prefix coefficients. [ForceClasses](GENERAL_FORCE_DESIGN.md)
uses explicit uniformly Cauchy force samples to construct acceleration names
and values. Actual finite coarse/fine errors now have a derived mesh-uniform
small-window bound in BarrowLib; bounded actual Newton schedules and
continuous-force local consistency are also checked. These realize force data
and control finite polygons. GeneralForcePrecision now derives monotone
geometric force precision. GeneralForceEndpoint uses actual calibrated
coarse/fine accumulation and a separate equivalent-duration comparison to
construct fixed-time central-force Cauchy names and values. This requires a
global Lipschitz comparison and bounds at actual coarse and first-half shadow
force arrivals; no motion-Cauchy field is assumed. The harmonic instance
derives those sample bounds and agrees with the old endpoint value.
GeneralForcePrefix adds bounds at actual represented-grid arrivals and derives
Cauchy names for every binary prefix. GeneralForceTime derives same-grid time
control, address independence, uniform prefix convergence and a continuous local
state/position map, with initial/zero cases and full-endpoint E/G agreement.
HarmonicGeneralTime derives all actual-grid bounds and equals the retained
harmonic maps. Generic finite telescoping, scalar grid differences, name-bound
scaling, time endpoints and prefix-to-value tails live in BarrowLib with old
public names preserved. Local-annulus stability, restart/gluing, general
interior-time E/G agreement and precision/partition independence remain open. B.1/B.2 now have the bounded results below;
integer-subdivision accumulation and dyadic E/G agreement are now proved. Both
kinds of coarse polygon alias are handled. HarmonicPathRegion now constructs
the matched region and finite-square outer-content lower cut, with a derived
vanishing cover. HarmonicPathContent realizes the cut as a Cauchy scalar
through proved shrinking intervals, independently of the initial cover.
Ordinary-area/Kepler-area identification remains distinct.

GeneralForceSecants now transfers the actual finite O(t²) position remainder
to rationally divided position differences of constructed curve values. Every
dyadic cell secant differs from its left-node velocity by at most H_m*B;
time continuity controls that node velocity against the target by H_m*K.
Thus the completed bracketing secants converge uniformly over every binary
address to its constructed velocity, with error H_m*(B+K), including the right
boundary. HarmonicSecants gives the retained-map corollary. KinematicEstimates,
SecantValues and DyadicNodes contain the derived finite remainders, proved
completed operators and actual time nodes; no desired rate is a field.
Unrestricted differentiation remains open; the acceleration secant bridge is
now derived below.

SampledValues now completes rational map samples using ordered comparisons and
vanishing error, deriving Cauchy and representative independence first.
CompletedForce applies it to the actual central-force precision family. The
extension is Lipschitz at completed positions, position-only, agrees with the
retained rational force values and is independent of the precision scale.
Actual prefix force samples have uniform budget (A*L+3*E0)/2^j against the
force at gammaValue. The harmonic extension equals scaling by -w along the
retained curve. GeneralForceAccelerationSecants now transfers actual finite
velocity remainders to completed dyadic velocity secants. At the left node the
error is L*H_m*V after the explicit rounding error vanishes. Force continuity
adds L*H_m*K against the target time. Precision-offset invariance is proved,
so the target is the same completed force at the actual constructed position.
Uniform convergence includes the right boundary; HarmonicAccelerationSecants
gives the retained-curve corollary. No force equation or desired derivative is
a premise. This is the dyadic bracketing criterion; unrestricted quotients and
external real-time identification remain open.

## One global family

Fix nonnegative rational T, initial state s, and harmonic coefficient w, with
T*(1+|w|)<=1/2. The level-j polygon has 2^j actual end-kick cells of duration
H_j=T/2^j. Existing HarmonicDyadic endpoint names instead rescale a complete
schedule separately for each rational sample time. Their uniform rational-time
control is checked. HarmonicConstructionAgreement now identifies their values
at reciprocal dyadic times with global prefixes by an exact finite index shift
and rational duration congruence. HarmonicDyadicAgreement now covers every
dyadic numerator using actual integer-subdivision accumulation. Explicit
finiteAddress constructions represent every k<2^m; zero/full-window endpoints
and equivalent represented Fraction parameters agree as well. An exact
three-tick example disproves finite schedule equality, while its completed
values are proved equal.

Use a binary address b to select intermediate times directly in the global
family: k_0=0, k_(j+1)=2*k_j+b_j, with b_j either0 or1. The intended level-j
approximants are the actual state after k_j cells and its actual elapsed time
k_j*H_j. HarmonicBinaryPrefix derives k_j<2^j, elapsed time<=T and state<=2M
before applying the actual comparison estimate. Its checked adjacent and
finite-gap bounds construct these state Cauchy names; see
[the checkpoint](OVERNIGHT-2026-10-03.md). BinaryTime now constructs their time
names and quotients the addresses by proved time-name equivalence. Identification
with an external real interval remains separate.

## Actual within-cell polygon names

HarmonicPolygonCurve constructs the affine position name at address b and
coarse level m from its actual prefix (x_m,v_m), with approximants
`x_m + (t_(m+j)-t_m)*v_m`. AffineValues proves the Cauchy condition and
`0 ≤ t_(m+j)-t_m ≤ H_m`; every approximant is on the actual coarse cell.
The planar value has distance at most

    R_m = [2*T*stateNorm(s) + prefixCoefficient(w,T,s)] / 2^m

to gammaPosition at the same address. Both terms are derived: the coarse
drift is bounded by H_m*2M, and the already proved prefix-to-value tail
supplies the other term. A positive-tolerance modulus gives convergence
uniformly over every address. These are whole-cell bounds, beyond vertices.
Equivalent addresses occupy the same coarse cell or adjacent cells. In the
adjacent case, actual neighboring cell positions share their vertex and affine
distance is controlled by the time-name gap. This proves boundary invariance
before polygonMap is lifted to the binary-time quotient. Zero time is handled
without dividing by T. The map inherits the whole-edge bound and uniform
convergence. The terminating/nonterminating half-time addresses give an explicit
different-cell control. No planar content or D_mesh is inferred.

HarmonicIntegerSubdivision derives exact unequal-cell defects and a finite
recurrence for k fine h-cells versus one k*h cell. With nonnegative h, h≤1 and
each finite partial duration≤1, the state discrepancy is at most h²*C(k,w,s),
where the coefficient is independent of h. Actual propagation over N blocks
now gives distance≤4*N*h²*quadraticCap(w,s,k). The same short window derives
all local-prefix conditions, coarse-state≤2M and both amplification bounds≤2.
For N=2^j and h=T/2^(m+j), this is C/2^j with
C=4*(T/2^m)²*quadraticCap(w,s,k). The existing prefix Cauchy condition removes
the finite shift m, proving equal names and values. The zero-tick case is
handled directly. This proves dyadic E/G agreement, without asserting general
confinement or P5. TimeCalibration separately proves finite/gauge unit invariance.

## Checked state-value construction

`CauchyValues.lean` now constructs a value space explicitly from state Cauchy
names. For two names a,b, the proved equivalence is

    for every positive rational eps, eventually
      stateNorm(a_j-b_j)<eps.

Reflexivity, symmetry and transitivity follow from the checked zero, symmetry
and triangle estimates. Values are the quotient by this proved equivalence.
Constant names embed rational states, and equality of their values is proved
equivalent to rational state value equivalence.

To express a closed distance bound between values, first define it on names:
for every positive rational eps, eventually stateNorm(a_j-b_j)<R+eps.
Representative invariance is proved before lifting this predicate to `Within`
on quotient values. Its triangle and symmetry properties, zero radius iff
equality, and convergence of constant approximants are checked.
The values must be constructed from the actual polygon names, with no supplied
limit point or completeness field. A generic completeness theorem and an
identification with an external real coordinate system are separate claims.

A nonconstant production control is available for the already checked endpoint
sequence at w=1,T=1/4,s=((1,0),(0,1)). Its level0 state differs from s by9/16,
while the fixed-time tail cap at level0 is3/8. A derived lower bound3/16 for
every later state difference can distinguish its quotient value from the
initial value. This arithmetic pin is a production-side control, not an
independent oracle. The all-level lower bound and quotient state separation
proof now compile. PositionValues separately proves position distance 135/512
at endpoint level 1 and a lower bound 39/512 for every later level, using the
state tail 3/16. Its positive projected endpoint/right-versus-left non-equality
proof supplies position separation, rather than inferring it from state separation.

## Checked time-domain map

BinaryTime derives geometric time tails and the positive-tolerance condition
from the actual ticks. Its time names define a proved equivalence of addresses.
HarmonicTimeRealization derives the arbitrary-prefix state bound and the
uniform same-grid state increment estimate from actual cells:

    stateNorm(S_j(b)-S_j(c)) <= 2*(1+|w|)*M*|t_j(b)-t_j(c)|.

Both states use the same duration T/2^j. The equivalence proof precedes the
quotient lift defining gammaValue. Closed time-radius R gives state-radius
2*(1+|w|)*M*R. The explicit tolerance half(eps)/(2*(1+|w|)*M+1)
gives state-radius half(eps), including zero initial magnitude.

The left value is the embedded initial state. The all-one right value equals
the complete-schedule endpoint value after bounding the last omitted cell.
Their time coordinates equal the embedded scalar times 0 and T, respectively;
the time-coordinate map is proved injective on the binary-time quotient.
The first-bit-only address1,0,0,... and address0,1,1,... give equal time and
state values, although their finite prefixes differ. At w=1,T=1/4 and level 2,
their time distance is 1/16, state factor 8, budget 1/2 and actual state
distance 8927/65536. These are production controls. Generic zero-time and
zero-state-magnitude values are constant. The sample right and left state
values differ by the already proved endpoint separation.

The domain is the explicitly constructed binary-time quotient. Its name/value
map is not a supplied curve or external limit point. PositionValues now derives
nonexpansive position and coordinate projections, their Cauchy-name/quotient
maps, constant compatibility and idempotence. Its PositionValue objects have
zero velocity component; gammaPosition inherits continuity, aliases, endpoints
and zero cases. Completed coordinate squares have two closed coordinate bounds
with a proved nonnegative radius. Eventual rational bounds imply membership;
the radius-1 square's corner (1,1) has L1 distance 2.
The same-time coarse polygon map is constructed on the binary-time quotient;
the actual harmonic matched region and its outer-content lower cut are now
constructed in HarmonicPathRegion. The velocity coordinate is now identified
as the uniform limit of completed bracketing dyadic position secants. Completed
dyadic velocity secants now converge uniformly to the completed sampled force.
Unrestricted difference quotients remain open. E/G identification is proved at
all common dyadic rational times. Other rational parameters and arbitrary
partition independence remain separate.

## Constructed between-path region and content

For each coarse cell, HarmonicPathRegion takes all rational convex connectors
between simultaneous quotient polygonMap and gammaPosition values, then their
closure in the completed plane. The region is the finite union of these cell
closures. It includes both maps, their shared initial endpoint and the final
connector. Rational interpolation descends only after Cauchy and equivalence
preservation are proved; completed coordinate squares are convex and remain
closed under positive-rational exhaustion. Reversing a connector leaves the
same region point, so opposite orientations cannot cancel.

The derived radius about the actual coarse start is

    R_m = C/2^m, C = 2*T*stateNorm(s) + prefixCoefficient(w,T,s).

One actual square per coarse cell covers the whole closed region, with budget

    B_m = 4*2^m*R_m² = 4*C²/2^m.

SquareOuterContent defines finite covers and their nonnegative summed budgets.
D_mesh is the exact closed lower cut of their infimum: q belongs precisely
when q is below every covering budget. Zero belongs, every lower bound is at
most B_m, and all lower bounds are eventually below any positive rational
tolerance. Empty/singleton regions have zero content; zero time gives D_mesh=0.
This is an actual region-dependent outer-content definition, with no supplied
area or curve. Crossings/overlaps count once in the region, whereas covering
sums count with multiplicity. See TRAJECTORY_DEFECT_REGION.md and the
[verification checkpoint](verification/constructed-path-content-2026-10-05.md).

HarmonicPathContent now constructs a scalar in the Cauchy quotient from this
cut. BoundedCuts starts with zero and a proved upper cover budget, keeps lower
membership and an upper bound for every content lower bound, and halves the
interval width exactly. The derived adjacent bound constructs the Cauchy
name. ScalarOrder proves representative invariance before lifting the rational
lower comparison; the scalar realizes exactly the all-cover cut. The value
is independent of the chosen initial cover and inherits nonnegativity, the
closed budget bound, zero time and convergence to zero. A known rational 1/3
cut recovers its embedded value for different initial budgets. Equality with
inner/ordinary area, Kepler swept-area transfer, arbitrary partition
independence, P5 and general-field whole-edge/content extension remain separate. No integral, ODE, measure theorem,
action constant or historical limiting premise is imported.
