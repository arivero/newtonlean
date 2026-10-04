# BarrowLib foundation migration, 4 October 2026

`BarrowLib` now contains finite rational geometry, dyadic arithmetic, and the
explicitly modern Cauchy-name quotient. Its imports point only to `BarrowLib`
and Lean core/Std. It asserts no historical dependency, central-force law,
trajectory, derivative, integral, or ODE theorem. The old
`NewtonLimitDynamics.Polygon.*` namespaces remain the declaration namespaces,
including for declarations compiled from `BarrowLib/`.

Whole-module moves: `TriangleBounds`, `ConvexCover`, and `BinaryTime`. Their old
paths are import-only facades. `CauchyValues` retains harmonic `timeValue`,
`binaryValue`, `endpointValue`, their bounds, and the harmonic sample; its
Cauchy-name quotient and general results live in `BarrowLib`. `PositionValues`
retains `gammaPosition`, its harmonic properties, and samples; projections,
nonexpansive maps, `PositionValue`, and coordinate squares live in `BarrowLib`.
The Newton-specific files import the generic modules directly.

The acyclic prerequisite chain is point algebra/bounds, state distance,
`EndpointCauchyName`, Cauchy values, and binary time. The moved declarations
include `stateSub`, `stateSub_congr`, `stateSub_norm_symm`,
`stateSub_triangle`, and `stateSub_self_norm_zero`; the latter three use the
existing generic state-distance triangle, symmetry, and self-zero results.
`blocks`, `duration`, their finite dyadic lemmas, `bit`, `ticks`, and tick
bounds now come from `DyadicArithmetic`. Generic rational negation and
`durationDifference` also moved there. Finite powers and their nonnegativity
moved to `FinitePower`; `dot` moved to point algebra. Generic rational
`le_add_cancel_left` is in `RationalMagnitudes`, with its old
`CauchyValues` name retained as a theorem alias.

`GeometricTail` proves finite-gap, two-sided, halving, doubling, and
positive-tolerance modulus results for any sequence of rational states with
adjacent error at most `A / 2^(j+1)` and a nonnegative rational `A`. Both
harmonic endpoint and harmonic binary-prefix tail theorems now instantiate
that result. Their coefficient definitions remain distinct:
`HarmonicDyadic.coefficient = 3*T²*|w|*stateNorm(s)`, while
`HarmonicBinaryPrefix.coefficient = T*stateNorm(s)*
(2*(1+|w|)+3*T*|w|)`. Each still derives its own adjacent-error bound from
actual harmonic schedules. `BinaryTime` reuses the same generic theorem with
coefficient `T` and an independently proved adjacent tick bound. None of
these estimates supplies motion convergence for an arbitrary central field.

Validation for this patch: Lean 4.19.0, `lake build`,
`lake build NewtonLimitDynamics`, `lake build BarrowLib`, and
`git diff --check`. These compile declared theorems; they do not certify a
historical proof or construct a continuous polygon-to-curve region.
