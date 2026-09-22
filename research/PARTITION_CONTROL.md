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

Next derive quantitative agreement between partitions at the same rational
time, including arbitrary positions inside their cells, and prove convergence
to the constructed map as their largest durations decrease. A rational-time
constant-force result must remain distinct from a general Euclidean-time
trajectory, a varying central-force realization and the historical limiting
argument. The displacement residual does not select an action constant.
