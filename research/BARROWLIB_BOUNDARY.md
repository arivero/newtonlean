# BarrowLib boundary inventory (Task D.1)

`BarrowLib` contains reusable finite rational geometry, ordered-ratio and
exhaustion arguments, elementary finite sums/products, and explicitly modern
Cauchy-name infrastructure. Its declarations may quantify over an arbitrary
point map or bound, but may not mention a particular force, kick schedule,
Newton proposition or edition, physical area/action, or a supplied trajectory.
It imports Lean core/Std only and has no derivative, integral or ODE primitive.
The Cauchy quotient is a modern construction, not a premise attributed to
Newton. Historical claims and force-law instances stay in `NewtonLimitDynamics`.

| Current location | Foundation content | Remains in NewtonLimitDynamics |
| --- | --- | --- |
| `Common/Quadratic` | All: `Magnitudes`, `Near`, `Ultimate`, enclosure and non-vacuity lemmas; `Ultimate` is an explicit formal encoding. | None. |
| `Common/RationalMagnitudes` | All `Fraction` arithmetic, `magnitudes`, `deflectionRatio`/`square_ratio` (generic quadratic ratios), `ratio`/`ultimate_congr`/`triangle_normalized_limit`, and finite `triangleArea`/`triangle_area_ratio`/`constructed_triangle_limit`. The last two limit theorems remain explicitly conditional on a supplied slope limit. | Historical interpretation of these generic ratio facts; the words “deflection” and “contact” in names/comments confer no historical premise. |
| `Common/FiniteGrowth` | All list weight/product/amplification bounds, including the arithmetic boundary examples; no motion parameter occurs. | None. |
| `Polygon/TimeSubdivision` | `Point`, `pointAdd`, `pointScale`, `pointNeg`, `pointSub`, `pointEquiv`, decidability/congruence (lines 9–54), plus `det`/`det_add_right` (182–194); `closedBoundaryTwice` is reusable finite determinant bookkeeping. | `positiveDuration`, `endKick`, `coarse`, `fine`, `totalDuration`, endpoint mismatch and the named kick examples, `directedConnector` and its example. The closed-boundary example stays with the Newton finite polygon. |
| `Polygon/PointBounds` | All coordinate L1 point/state definitions and bounds. Record that this is a chosen coordinate magnitude, not an intrinsic physical norm. | None. |
| `Polygon/TriangleBounds` | All determinant/unsigned triangle bounds, transformations and sign-control examples; sums count patches with multiplicity. | The Newton interpretation of polygon versus curve area remains outside. |
| `Polygon/ConvexCover` | `UnitInterval`, rational interpolation, point-subtraction/triangle lemmas, L1 ball and square enclosure, and `matchedPatch` bounds. The latter is a generic quadrilateral construction despite the current physical-time comment. | Any claim that these covers define the polygon–curve area or a region's area. |
| `Polygon/CauchyValues` | `distance`, `NameEquiv`, `Value`, `realize`, `constantName`, `embed`, `NameBound`, `Within`, and their generic results through `within_zero_iff` (line 463), including `constant_approximants_converge`; move `le_add_cancel_left` (515) to generic Fraction arithmetic. | `timeValue`, `binaryValue`, their harmonic bounds, `endpointValue`, and the harmonic sample (465–514, 536–end). |
| `Polygon/BinaryTime` | Binary tick/time approximation, Cauchy time names, `AddressEquiv` and quotient `BinaryTime`: no force appears in their statements. | The identification of those names with harmonic prefixes/realized motion. |
| `HarmonicDyadic`, `HarmonicBinaryPrefix`, `HarmonicAccumulation` | Extract only coefficient-parameter dyadic tail algebra (`tailCap`, `doubleTail`, halving, doubling, precision modulus, and the finite-gap/two-sided argument under an abstract adjacent-error bound), `two_pow_ge_succ`, and generic `fpower`/`fpower_nonnegative`. | Distinct endpoint/prefix coefficients, `adjacentCap_tail`, schedule errors, small-time premises, and the harmonic instances of the generic tail results. Their different coefficients must not be identified. |

**Acyclic extraction order.** Move `Quadratic` before `RationalMagnitudes`:
the latter currently imports the former. Extract point algebra and determinant
from `TimeSubdivision` next; then `PointBounds`, `TriangleBounds` and
`ConvexCover`. Extract `HarmonicComparison.stateSub`,
`HarmonicDyadic.stateSub_congr`/`stateSub_norm_symm`, and
`HarmonicAccumulation.stateSub_triangle`/`stateSub_self_norm_zero` to a generic
state-distance module after `PointBounds`. `EndpointCauchyName` currently lives
in `HarmonicDyadic` (line 331); move it after that distance module and before
the generic `CauchyValues` core. The current `CauchyValues →
HarmonicBinaryPrefix → HarmonicDyadic` import must be replaced by this direct
generic dependency; only a Newton-side value-instances file imports both.
Similarly extract `HarmonicBinaryPrefix.bit`/`ticks`,
`HarmonicDyadic.blocks`/`duration`/`duration_halving`, and the scalar
`HarmonicTimeComparison.durationDifference` to generic dyadic/time arithmetic
before moving `BinaryTime`. `BinaryTime` then imports the generic quotient and
dyadic modules, never a harmonic module. Generic tail arithmetic imports only
Fraction and generic distance/triangle results; harmonic coefficients import
it in the opposite direction.

For migration, retain existing fully qualified declaration names where
practical by using their current `NewtonLimitDynamics.*` namespaces inside
`BarrowLib` files. Fully migrated old modules become import-only compatibility
facades; mixed modules such as `TimeSubdivision` and `CauchyValues` import the
new generic file and keep only their Newton-specific declarations. Remove
original definitions to avoid duplicates. No `BarrowLib` file imports an old
facade or mixed module. Add the separate `lean_lib` and update
catalogues/references/checks in D.2, after verifying each layer.

Task A can start before the full D.2 migration by bootstrapping the minimal
`BarrowLib` chain (`Quadratic`, Fraction arithmetic, point algebra and
`PointBounds`) with those facades. Put new generic `Point → Point` Lipschitz,
growth/confinement and parameter-coefficient tail estimates under
`BarrowLib/` immediately. State them without `CentralSchedule.Field` or a
harmonic `w`; Newton-side modules instantiate them for central/parallel laws.
This small bootstrap and its library registration are part of A's verified
increment; D.2 migrates the remaining generic modules and completes the
catalogue, count and verification-command changes. Every new generic estimate
is therefore in the foundation from its first checked version.
