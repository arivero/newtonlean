# Area of the constructed intervening region

HarmonicPathRegion now constructs a matched polygon–curve region and its
finite-square outer content in Lean. This is a `modern_reconstruction`,
separate from the historical claims in De Motu, 1687 and 1713. The curve is
constructed from the actual harmonic polygons; no curve, area function or
covering inequality is supplied. See [path defect](PROP_I_PATH_DEFECT.md) and
[the construction ledger](CAUCHY_REALIZATION.md).

The general map's constructed velocity now has the completed dyadic secant
bridge. CompletedForce additionally constructs the force at completed positions
and uniformly identifies the limit of actual prefix force samples. This force
extension also applies to the retained harmonic curve. Completed dyadic
velocity secants now converge uniformly to that force; unrestricted-rate and
area interpretations remain separate.

Fix T>=0, initial state s and harmonic coefficient w with
T*(1+abs(w))<=1/2 in the retained tau=1 compatibility gauge. The completed
planar type is PositionValue. The continuous curve gammaPosition and the
level-m coarse polygonMap are already proved maps on the same binary-time
quotient. Equivalent same-cell and shared-boundary addresses give one polygon
point. E/G agreement at every dyadic rational time is retained.

For cell k, take every rational convex connector between simultaneous
polygonMap(t) and gammaPosition(t), where an address of t has level-m tick k.
ConvexValues constructs the interpolated Cauchy name and proves name-equivalence
preservation before quotient lifting. The cell region is the closure of these
connector points, using every positive rational tolerance in the completed
plane. The whole region is the union of the 2^m cell closures. This is a named
closed-rational-connector candidate; identification with a different Euclidean
bounded-region convention requires its own proof.

Both maps belong to the region. Their initial endpoints are proved equal to
the initial point. The explicit final connector from polygonMap(T) to the
constructed endpoint value is included even when finite endpoints differ.
Reversing a connector leaves the same point. All crossing lobes therefore
remain in this unsigned point set; overlapping portions count once. Finite
square budgets count overlap with multiplicity and serve as upper bounds.
No absolute value of a signed Kepler difference defines the region or content.

CompletionGeometry proves closed coordinate-square bounds by rational
exhaustion, square preservation under closure, and exact closed bounds for
embedded rational points. Rational convex interpolation preserves a square
containing both endpoints. The harmonic polygon drift and prefix-to-curve
tail put both actual simultaneous endpoints in the square about their actual
coarse start with radius

    R_m = C/2^m,
    C = 2*T*stateNorm(s) + prefixCoefficient(w,T,s).

One square per coarse cell therefore covers the entire region, with derived
nonnegative budget

    B_m = 4*2^m*R_m² = 4*C²/2^m.

SquareOuterContent defines an arbitrary finite square cover by its actual
square family and containment proof. Its budget is the sum of 4*R². The
outer content is the closed rational lower cut of the infimum of *all* such
budgets: q belongs exactly when it is below every cover budget. The definition
depends on the actual region, independently of the selected upper cover.
Zero belongs, lower bounds are downward closed, rational exhaustion closes
the cut, and region inclusion preserves content order. Empty and singleton
regions have exactly zero content.

HarmonicPathRegion.D_mesh is this cut for the actual matched region. Every
lower bound is at most B_m, and an explicit positive-tolerance modulus makes
all lower bounds less than any prescribed positive rational tolerance. Zero
time has zero content. These are checked geometric containment and exhaustion
results. HarmonicPathContent now realizes the lower cut as a Cauchy scalar,
using BoundedCuts' derived interval widths B/2^n and adjacent bound. Its rational
lower comparisons are exactly the all-cover infimum cut. The value is independent
of the initial cover and inherits scalar nonnegativity, budget control, zero
time and decay. Equality with inner content, ordinary Euclidean area or a
measure remains separate.
P5 unrestricted-rate, leading curved potential steps, arbitrary-partition independence,
gluing and general central-force whole-edge/content extension remain open.
GeneralForceTime now constructs a local continuous binary-time state/position
map under explicit global Lipschitz comparison and actual/coarse/shadow sampled
force bounds; its harmonic instance equals the maps used in this region.
GeneralForceSecants now identifies constructed velocity as the uniform limit
of the actual completed curve's bracketing dyadic position secants; the
retained harmonic curve inherits this result. GeneralForceAccelerationSecants
now gives the complementary completed dyadic velocity-secants/force bridge.
Unrestricted differentiation and the leading curved potential step remain open. No integral,
ODE, measure or quantum premise closes them.

Verification details are in the
[content checkpoint](verification/constructed-path-content-2026-10-05.md).
