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

Next accumulate position/velocity differences between evolving schedules and
derive nonnegative area control, then construct the trajectory with an explicit
time domain and partition independence. Local identities cannot simply be
summed as though coarse/fine initial cell states stayed equal. No actual curve,
global accumulation, completion or ODE theorem is supplied by these increments.
