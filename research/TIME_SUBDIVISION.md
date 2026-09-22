# One finite common-force time subdivision

This is a modern coordinate reconstruction for the refinement obligation in
[the Section II map](SECTION_II.md), not a historical proof or a claim that
Newton selected this scheduling convention. It constructs finite polygons
without assuming a limiting trajectory or using integral calculus.

Choose positive rational durations `h` and `k`, with coarse duration `h+k`,
and common initial position `p`, velocity `v`, and constant accelerative force
`a` (force per unit mass). In each cell of duration `d`, drift from `p` to
`p+d*v`, then apply the velocity impulse `d*a` at the right endpoint. The
terminal impulse changes velocity but adds no displacement in that cell.

The coarse endpoint is `C = p+(h+k)*v`. The fine polygon first reaches
`B = p+h*v`, receives impulse `h*a`, and then reaches
`D = B+k*(v+h*a)`. Its final impulse is `k*a`. Thus the two constructions
use the same initial data, total duration and force coefficient, with matching
total impulse. Their terminal velocities agree, while

`D = C + (h*k)*a`.

This mismatch is a failure of exact nesting for this convention. It does not
establish failure of trajectory existence, fixed-force nonuniqueness or an
obstruction to a different classical scheduling convention.

To compare enclosed finite areas when `D` differs from `C`, close the boundary
explicitly: traverse `p → B → D`, add the straight connector `D → C`, and
return along the reversed coarse edge `C → p`. The connector is geometric
bookkeeping at the shared terminal time, not an additional mechanical cell.
The determinant sum of this boundary is a signed doubled polygon area; its
absolute value is not by itself a bound on position error or on sums of
absolute cell defects.

For the rational example `h=k=1/2`, `p=(0,0)`, `v=(1,0)`, `a=(0,1)`,
the intermediate vertex is `B=(1/2,0)`, the coarse endpoint is `C=(1,0)`,
and the fine endpoint is `D=(1,1/4)`. The connector has displacement
`(0,-1/4)`. The closed boundary has signed doubled area `-1/8` under the
displayed orientation. This scalar is a finite defect between constructed
polygons, not the area between a polygon and an assumed curve.

The Lean implementation uses the existing signed `Fraction` representatives;
coordinate equalities mean cross-multiplication equivalence, not equality of
unnormalized numerator/denominator records. Its algebraic mismatch and velocity
identities hold for arbitrary rational inputs; positive-duration facts give
the intended mechanical specialization.

The finite-partition follow-up is now implemented in
[PartitionControl](PARTITION_CONTROL.md): it derives exact endpoint formulas
and a largest-cell coefficient bound from the constructed schedules, and
`PartialCell.lean` extends both to positions inside a cell. The next
obligation is rational-time convergence across partitions,
tracking non-nested endpoints and connectors explicitly. Keep finite sums of
absolute defects separate from signed cancellation. A general justified limiting
time-to-position map, partition independence and continuous-force
identification remain later obligations. No action constant is selected here.
