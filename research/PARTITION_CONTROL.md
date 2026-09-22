# Finite partition control: constant accelerative force

This continues [the two-cell comparison](TIME_SUBDIVISION.md) with the same
end-of-cell impulse convention and common initial position `p`, velocity `v`
and constant accelerative force `a`. It is a modern finite coordinate
reconstruction, not a proof of Newton's general central-force argument.

## Recurrence and physical interpretation

Represent a finite schedule by natural-number weights `w_i` and a positive
common denominator `D`. Cell durations are `w_i/D`. Nonnegative weights allow
degenerate zero-duration cells in the arithmetic; a mechanical subdivision
with strictly positive cells additionally requires `w_i>0` on its used prefix.
This representation admits unequal rational cells. No integer time lattice is
being imposed on the physical durations.

Construct the motion by successively applying `TimeSubdivision.endKick`.
Alongside it construct three natural-number coefficients:

```
T_0 = A_0 = Q_0 = 0
T_(j+1) = T_j + w_j
A_(j+1) = A_j + w_j*T_j
Q_(j+1) = Q_j + w_j*w_j
```

`partitionMotion_formula` proves the exact state identities, with rational equivalence:

```
velocity_j = v + (T_j/D)*a
position_j = p + (T_j/D)*v + (A_j/D²)*a.
```

`stats_identity` proves `2*A_j+Q_j=T_j²`. Each `w_i≤M` gives
`w_i²≤M*w_i`, hence `Q_j≤M*T_j`. Both are finite arithmetic results.

## Constructed candidate and remaining bridge

Define an algebraic map on rational times by
`q(t)=p+t*v+(t²/2)*a`. This is a construction whose relationship to the
polygon recurrence is proved here; calling it a polynomial alone supplies
neither mechanical interpretation nor convergence. The recurrence identities give
the exact residual

`q(T_j/D) = position_j + (Q_j/(2D²))*a`.

`residual_mesh_bound` proves its scalar coefficient is at most
`M*T_j/(2D²) = (largest-duration bound)*(elapsed time)/2`.
The vector residual points along `a`; coordinate magnitudes also depend on
the corresponding acceleration component. A bound on the coefficient is
not a force-independent position bound.

This comparison involves positions, not swept sectors. It does not yet sum
absolute polygon-strip defects. For comparison areas, retain explicit closing
connectors between non-nested endpoints as in the two-cell construction.

## Positions inside a cell

`Polygon/PartialCell.lean` extends the schedule by a partial final cell of
duration `u/D`, with `u` a natural numerator. The partial position is the
actual prefix position drifted by the actual prefix velocity. It is the
position component of one further end-kick step, and
`endKick_position_kick_free` records that the terminal kick leaves that
position unchanged. `partialState_append` identifies the construction with
the recurrence on `weights ++ [u]`, so the statistics are derived as
`T+u` and `Q+u*u` (`total_append`, `squares_append`) and are not postulated.
`candidate_partial_residual` then gives the exact residual

`q((T+u)/D) = partialPosition + ((Q+u*u)/(2D²))*a`.

For a designated next cell of weight `w` with `u≤w` (and `0≤u` from `Nat`),
prefix weights at most `M` and `w≤M`, `partial_squares_bound` proves
`Q+u*u≤M*(T+u)`, and `partial_residual_mesh_bound` gives the Fraction
coefficient bound `(Q+u*u)/(2D²) ≤ M*(T+u)/(2D²)`. The hypothesis `u≤w` is
used. Boundaries: `partial_zero` (u=0 gives the prefix vertex),
`partial_full_cell` (u=w gives the next actual vertex) and
`partial_zero_force` (a=0 gives the inertial map at `(T+u)/D`).

This is a finite position estimate at rational sample times inside a cell.
It asserts no convergence and does not assume that old vertices survive
refinement.

## Small residual under explicit refinement

`Polygon/UniformRefinement.lean` proves `uniform_refinement_small`: for each
positive rational tolerance `ε` and rational time `N/E`, refining by
`K = N*den(ε)+1` into unit cells over denominator `E*K` reaches the same time
(`refined_time`) with residual coefficient `Q/(2D²) ≤ ε`. The witness is
explicit. It is one refinement per tolerance; arbitrary partitions are covered
by the earlier mesh bound.

## Comparing two partitions at one rational time

`Polygon/PartitionComparison.lean` proves `partition_comparison`: two
arbitrary schedules, with possibly different denominators `D, E` and cells,
whose end times are equivalent rationals, satisfy

`position + (Q/(2D²))*a = position' + (Q'/(2E²))*a`.

`candidate_time_congr` supplies the time congruence it needs. With
`residual_mesh_bound` on each side, the two actual positions differ along `a`
by a coefficient between zero and the larger mesh coefficient. Partition
dependence at a common rational time is thus exact and controlled by the mesh.
An explicit difference inequality is not yet packaged. Velocities have the
form `v + (T/D)*a` by `partitionMotion_formula`, so they agree whenever the
times agree; that corollary is also not yet packaged.

Next combine the partition comparison with the within-cell estimates to reach
arbitrary rational sample times inside cells, and prove convergence
to the constructed map as their largest durations decrease. A rational-time
constant-force result must remain distinct from a general Euclidean-time
trajectory, a varying central-force realization and the historical limiting
argument. The displacement residual does not select an action constant.
