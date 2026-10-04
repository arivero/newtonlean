# Constructing motion from the harmonic polygon family

This is the next-step specification for Proposition I's construction variant,
not a checked trajectory theorem. The mathematical layer is a modern
reconstruction with explicit rational coordinates and the calibrated L1 state
magnitude. It does not add a historical dependency or silently supply a curve.
The stage-local obligations remain in [the realization ledger](PROP_I_REALIZATION.md).

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
[the checkpoint](OVERNIGHT-2026-10-03.md). Binary addresses have not yet been
identified with a completed time interval.

## Point-space realization specification

After the prefix names are checked, construct a point space explicitly from
state Cauchy names. For two names a,b, the proposed equivalence is

    for every positive rational eps, eventually
      stateNorm(a_j-b_j)<eps.

Prove reflexivity, symmetry and transitivity from the checked zero, symmetry
and triangle estimates. Define values as the quotient by this proved
equivalence. Constant names embed rational states. Equality of constants must
respect rational value equivalence; a constructor name alone does not prove
that different physical states remain distinguishable.

To express a closed distance bound between values, first define it on names:
for every positive rational eps, eventually stateNorm(a_j-b_j)<R+eps. Prove
that this predicate is invariant under replacing either name by an equivalent
one before lifting it to the quotient. Establish its triangle and symmetry
properties and the convergence of constant approximants to their name's value.
The values must be constructed from the actual polygon names, with no supplied
limit point or completeness field. A generic completeness theorem and an
identification with an external real coordinate system are separate claims.

A nonconstant production control is available for the already checked endpoint
sequence at w=1,T=1/4,s=((1,0),(0,1)). Its level0 state differs from s by9/16,
while the fixed-time tail cap at level0 is3/8. A derived lower bound3/16 for
every later state difference can distinguish its quotient value from the
initial value. This arithmetic pin is a production-side control, not an
independent oracle, and the quotient separation proof remains to be checked.

## Time-domain identification specification

The binary time approximants have geometric tails. Construct their time names
and an equivalence of addresses based on vanishing time difference. Derive a
uniform same-grid state increment bound from actual cells and prefix state
bounds. Use it to prove that equivalent time addresses give equivalent state
names. Only then lift the address-to-value construction to a map on the
constructed time quotient and prove continuity there. The two addresses of a
dyadic time must agree in value. Identify the right endpoint with the existing
complete-schedule endpoint name, accounting for the last omitted cell.

These are explicit obligations. An arbitrary function from binary addresses
to state classes does not yet establish a motion on times. Likewise, the
existence of names does not identify their velocity coordinate with the
derivative of position or their acceleration with the sampled harmonic force.

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

Partition independence, force identification, extension beyond the named short
interval and the general central-field case remain separate. No Kepler-area
cancellation, later ODE theorem or quantum premise closes any of them.
