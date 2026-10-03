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
to these factors, and bounding their accumulated error, remain next.

Next bound the accumulated expression uniformly as the mesh shrinks, derive
nonnegative area control, then construct the trajectory with an explicit time
domain and partition independence. The finite error recurrence supplies no
completion, continuum curve or ODE theorem. Its uniform refinement bound is
the next target recorded in the overnight checkpoint.
