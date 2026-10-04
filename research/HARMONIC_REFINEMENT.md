# Harmonic refinement without a supplied trajectory

This finite construction supports Proposition I's primary realization route.
It is a modern rational reconstruction of a particular central field; the
three historical targets remain separately scoped in PROP_I_PATH_DEFECT.md.

`HarmonicRefinement.lean` compares actual cells of the SAME field a(x)=-w*x
with the SAME initial position x and velocity v: one duration 2h and two
durations h. The total time is equal. Physical time/inward-force interpretation
requires h>0 and w>0; the arithmetic also covers zero and signed parameters.

For y=x+h*v, fine endpoint z and coarse endpoint X, the checked formulas are
z=X-h²*w*y and v_fine=v_coarse+h²*w*v+h³*w²*y. The endpoints need not coincide.
The directed connector z→X closes the comparison and is not a mechanical cell.
Its signed doubled boundary area is

    det(x,y)+det(y,z)+det(z,X)-det(x,X).

`closed_eq_triangle` identifies this with triangle y,z,X; `closed_defect_cubic`
gives exactly -h³*w*det(x,v). The local absolute magnitude is nonnegative.
`swept_equal` proves the two separate Kepler sums agree. This is a comparison
of force/time-compatible constructed polygons, not arbitrary supplied paths.

The exact example w=1, h=1/2, x=(1,0), v=(0,1) has y=(1,1/2), z=(3/4,7/8),
X=(1,1), both Kepler doubled sums 1, closed doubled defect -1/8 and absolute
gap 1/8. Lean checks all values and nonzero defect; a false zero-defect
assertion in a temporary Lean file was rejected.

`PointBounds.lean` now supplies coordinate L1 magnitudes for rational points
and position/velocity states, with nonnegativity, equivalence invariance,
triangle estimates and scaling. This coordinate diagnostic is not an area;
combining position and velocity physically also requires a calibration of units.
`HarmonicComparison.lean` derives, from the actual drift and kick,

    stateNorm(cell(w,h,s)) ≤ (1+|h|)*(1+|h|*|w|)*stateNorm(s).

The cell applied to the difference of two initial states is equivalent to the
difference of their actual outputs. Consequently the same factor bounds their
one-step perturbation. These statements cover signed and zero parameters.
At w=1,h=1/2 the factor is 9/4, the initial state norm is 2 and the actual
one-cell state norm is 11/4. Zero-duration controls and a rejected false
norm-cancellation assertion check the boundaries of the estimate.

`HarmonicAccumulation.lean` now compares evolving schedules. From the same
initial state s it constructs C_n from n cells of duration 2h and F_n from
2n cells of duration h, with their equal elapsed times proved. Put

    k=(1+|h|)*(1+|h|*|w|), r=k², b=kappa(w,2h),
    delta=|h|²*|w|*(k+1), M=stateNorm(s),
    B_0=0, B_(n+1)=r*B_n+delta*b^n*M.

The local truncation estimate is derived from the actual position/velocity
mismatches, and two fine cells propagate an input error by at most r. Induction
then proves `stateNorm(C_n)≤b^n*M` and
`stateNorm(F_n-C_n)≤B_n` for every n, with B_n nonnegative. This addresses the
different initial states of later coarse/fine cells explicitly. The checked
one-block state error is 13/16 and its budget 13/8; two blocks give an actual
state error of 173/256. These are coordinate state errors, separate from D and K.

`Common/FiniteGrowth.lean` proves the finite product estimate used for uniform
refinement control. For a positive common denominator D and nonnegative
integer increments a_j, put S=sum(a_j) and P=product(D+a_j). Finite induction
gives `P*(D-S)≤D^(length+1)`. The condition `2*S≤D` then gives
`P/D^length≤2`, independently of the number of increments. Empty and zero
increments are covered; a checked counterexample shows the bound fails when
the small-total condition is removed. Transporting the actual harmonic powers
to these factors is now proved in `HarmonicUniform.lean`.

For h≥0, T=2nh and `T*(1+|w|)≤1/2`, that module proves both actual
amplification powers are at most 2. It identifies the displayed T with the
elapsed time of each actual list, bounds both state magnitudes by 2M, and
derives

    stateNorm(F_n-C_n) ≤ 3*T*h*|w|*M.

The constants use the chosen coordinate/unit calibration; this is not a
universal physical time threshold. Zero blocks and zero durations are covered.
The boundary example w=1,h=1/8,n=1 has T=1/4, actual state error 145/4096
and bound 3/16. A false unrestricted factor-two claim is rejected: w=h=n=1
has fine amplification 16. Thus the finite accumulated bound is uniform in
refinement at fixed sufficiently small total time.

Next construct finite Cauchy data, then realize the trajectory with an explicit
time domain and partition independence. The finite estimates supply no
completion, continuum curve or ODE theorem. Position/velocity error and
geometric area remain distinct obligations in the primary construction.

`TriangleBounds.lean` supplies the next area estimates in rational coordinates:
`abs(det(u,v))≤pointNorm(u)*pointNorm(v)`, and corresponding bounds for the
unsigned doubled magnitude of an actual triangle. This magnitude is
nonnegative, translation invariant and unchanged by exchanging its last
two vertices. Opposite signed triangles can have zero signed total and a
positive unsigned patch sum. That sum counts multiplicity; geometric coverage
or decomposition of the intervening region must still be derived. It is
separate from either path's Kepler swept triangles.

`ConvexCover.lean` and `HarmonicCover.lean` now derive a finite geometric
enclosure. Each coarse block is divided into two matched half-cell patches:
both paths use the same rational physical-time fraction, and a second fraction
interpolates between their simultaneous positions. The coarse midpoint is a
subdivision of its drift and receives no impulse. Prefix state/error bounds
place all six actual corners in the L1 ball, hence the coordinate square, of
radius

    R = h*M*(4+3*T*|w|)

about the coarse start. Convex interpolation proves containment for every
pair of rational unit-interval parameters. One square covers both half-cell
patches. Summing one square per coarse block gives the nonnegative budget

    4*n*R² = 2*T*h*M²*(4+3*T*|w|)².

The sum counts multiplicity; it is not a theorem about union content or the
actual area D_mesh. At fixed T,w,M its formula has a factor h. The boundary
example has radius 19/16 and budget 361/64. A quarter-radius L1 ball fails for
the fine endpoint; a separate eighth-radius coordinate square fails for the
coarse endpoint. These controls do not identify the ball with the square.
No trajectory was supplied or constructed by this finite cover.

`HarmonicDyadic.lean` constructs fixed rational-time endpoint Cauchy data.
For T≥0, level j runs 2^j actual cells of duration T/2^j. Value equivalence,
rather than identical rational representatives, identifies these runs with
the checked coarse/fine schedules and proves their common elapsed time T.
Under T*(1+|w|)≤1/2, with A=3*T²*|w|*M, it derives

    stateNorm(D_(j+k)-D_j) ≤ A/2^j
    stateNorm(D_m-D_n) ≤ 2*A/2^N  when m,n≥N.

An explicit modulus N=(2*A.num*eps.den).toNat makes the latter budget strictly
less than any represented rational eps with positive numerator. The proof is
finite integer induction using 2^N≥N+1; no completeness premise is imported.
`endpointName` packages the actual approximants and their derived Cauchy proof.
The modulus is deliberately large and representation dependent; it is not an
efficient evaluation algorithm or a physical scale. Zero time returns the
initial state in value equivalence at every level. The boundary adjacent
error145/4096, adjacent cap3/16 and tail cap3/8 compile.

`HarmonicTimeComparison.lean` derives a uniform time-parameter estimate for
these actual endpoint schedules. For nonnegative T,U satisfying the same
small-time condition, every level obeys

    stateNorm(D_j(U)-D_j(T)) ≤ L*|U-T|,  L=4*(1+2*|w|)*M.

The cell count agrees while the durations differ; this comparison is distinct
from common-time refinement. Actual one-cell mismatch, derived prefix state
bounds and finite amplification give the estimate. `timeName` constructs the
map from admissible rational times to Cauchy names. For every positive rational
eps, delta=eps/(L+1) is positive and controls every approximant at once, including
M=0. The production control w=1,T=1/4,U=1/8,j=0 has exact error19/64,
L=24 and bound3. Same-time and zero-state conclusions are generic.

This constructs a uniformly continuous rational-time map of Cauchy names.
Realization in a completed point space, identification with prefixes of one
global polygon family, partition independence,
mechanical force identification and the actual intervening-region area remain
separate obligations. In the general represented-point model, a force must
also respect point value equivalence; the harmonic cell's compatibility is
derived in this construction rather than assumed for arbitrary fields.

`HarmonicBinaryPrefix.lean` constructs intermediate-time Cauchy data directly
from one global polygon family. An arbitrary binary address selects ticks
k_0=0, k_(j+1)=2*k_j+b_j. The proof derives k_j<2^j and runs exactly k_j
actual cells of duration T/2^j. Its actual elapsed time is at most T, and
both compared prefix states have magnitude at most2M. The optional extra fine
cell has increment at most2*h*(1+|w|)*M; common-time refinement supplies the
other error. With

    A = T*M*(2*(1+|w|)+3*T*|w|),

the actual adjacent error is at most A/2^(j+1), an arbitrary finite gap from
level j is at most A/2^j, and two levels m,n>=N differ by at most2*A/2^N.
Finite integer arithmetic constructs a positive-tolerance modulus and
`prefixName` packages the actual approximants with their derived Cauchy proof.
The all-zero address returns the initial state exactly; zero time returns it
in value equivalence. Production controls give first error17/64, A19/8 and
same-time second error545/65536. No actual curve or limit point was supplied.

These are Cauchy data for all binary addresses. Identification of equivalent
time descriptions, continuity of the resulting
time-to-position map and the actual between-path region remain to be proved;
see [the construction specification](CAUCHY_REALIZATION.md). The independently
rescaled rational-time endpoint map and this single global family remain
distinct until their values are compared.

`CauchyValues.lean` realizes these names in an explicitly constructed quotient
value space. Eventual distance below every positive rational tolerance is
proved to be an equivalence relation. Constant rational states embed into the
quotient, and their values are equal exactly when their state coordinates are
value-equivalent. No external limit point or completeness field is supplied.

A closed rational-radius bound is defined first on names using eventual
distance<R+eps for every positive eps. Its invariance under both representative
changes is proved before lifting `Within` to values. Symmetry, the triangle
bound, zero radius iff equality and convergence of constant approximants are
checked. Actual endpoint/time/binary-prefix constructors give values with the
existing time and prefix-tail bounds. The example endpoint value differs from
the initial value: its level0 distance9/16 and tail3/8 imply distance>=3/16
at every level, which rules out name equivalence.

This constructs state values, including a uniformly controlled rational-time
map. Identification of binary addresses as times and a well-defined continuous
map on their quotient remain next. A state separation result does not by itself
prove position-only separation or any intervening-region area. Generic
completeness, external real-coordinate identification and mechanical properties
are not inferred.
