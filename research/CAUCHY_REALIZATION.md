# Constructing motion from the harmonic polygon family

This records the checked Cauchy-name, value and binary-time constructions and
the remaining geometric and mechanical steps for Proposition I's construction
variant. It is not a completed trajectory theorem. The mathematical layer is a modern
reconstruction with explicit rational coordinates and the calibrated L1 state
magnitude. It does not add a historical dependency or silently supply a curve.
The stage-local obligations remain in [the realization ledger](PROP_I_REALIZATION.md).

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
and control finite polygons, not the general motion. Geometric precision
selection, general polygon Cauchy names and restart/gluing remain open; the
generic extraction is complete; B.1/B.2 follow next.

## One global family

Fix nonnegative rational T, initial state s, and harmonic coefficient w, with
T*(1+|w|)<=1/2. The level-j polygon has 2^j actual end-kick cells of duration
H_j=T/2^j. Existing HarmonicDyadic endpoint names instead rescale a complete
schedule separately for each rational sample time. Their uniform rational-time
control is checked, but identifying those values with prefixes of this global
family requires a further comparison. It is not an identity of schedules.

Use a binary address b to select intermediate times directly in the global
family: k_0=0, k_(j+1)=2*k_j+b_j, with b_j either0 or1. The intended level-j
approximants are the actual state after k_j cells and its actual elapsed time
k_j*H_j. HarmonicBinaryPrefix derives k_j<2^j, elapsed time<=T and state<=2M
before applying the actual comparison estimate. Its checked adjacent and
finite-gap bounds construct these state Cauchy names; see
[the checkpoint](OVERNIGHT-2026-10-03.md). BinaryTime now constructs their time
names and quotients the addresses by proved time-name equivalence. Identification
with an external real interval remains separate.

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
The same-time coarse polygon map and actual between-path region are next.
The velocity coordinate still needs to be identified
with position's rate of change, and acceleration with the sampled harmonic
force. Partition independence and identification with independently rescaled
rational-time endpoint values remain separate.

## Between-path geometry specification

For a fixed coarse level m, compare its actual position at a constructed time
with the position value of the constructed motion at that same time. The
intervening set must consist of the connectors between these simultaneous
positions, with endpoint connectors stated explicitly. It is separate from
the radius-swept Kepler set. Retain every lobe when connectors cross and state
whether an area is union content or a cover counted with multiplicity.

A candidate route is a square about each actual coarse start. Its radius must
be derived from both a refinement tail and motion within that coarse cell.
The twelfth unit's checked state tail suggests the conservative radius

    R_m = H_m*M*C,  C=2*(1+|w|)+3*T*|w|,
    summed square budget = 4*T*H_m*M²*C².

These are future proof targets, not checked trajectory-cover theorems. The
prefix tail controls later selected states relative to the level-m coarse
start; the coarse edge itself needs its independently derived drift bound.
Prove closure of the square predicate under name equivalence and rational
convex interpolation before transferring any finite cover to quotient values.
Then derive a finite nonnegative cover budget and its explicit positive-
tolerance decay. A small square sum proves a small outer enclosure only after
the intervening set is shown to lie in those squares; it does not define that
set's area or establish measurability. Exact union/content or a stated outer-
content construction remains necessary for an actual scalar D_mesh.
The [region specification](TRAJECTORY_DEFECT_REGION.md) fixes the intended
simultaneous-position connector set and finite-square outer content before
the geometric proof is attempted.

Partition independence, force identification, extension beyond the named short
interval and the general central-field case remain separate. No Kepler-area
cancellation, later ODE theorem or quantum premise closes any of them.
