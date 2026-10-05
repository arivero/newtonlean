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


## D.2 extraction, 4 October

The remaining geometry, state-distance, Cauchy-name/quotient, dyadic arithmetic,
binary-time and generic position-value layers now live under `BarrowLib/`.
Mixed Newton files import the generic definitions and retain the force-specific
instances; whole migrated modules are old-path compatibility imports. Existing
fully qualified declaration names remain stable. The generic finite triangle
and cover examples still make no physical region-area assertion.

`GeometricTail` proves the coefficient-parameter finite-gap/two-sided estimates
and a positive-tolerance modulus from an explicit adjacent bound. The actual
harmonic endpoint and prefix constructions supply that bound through their
own finite refinement estimates and retain their different coefficients.
No generic Cauchy premise is counted as a derived mechanical estimate.
The completed position projections and coordinate squares also move to the
foundation; the harmonic gamma maps and samples remain Newton-side.

The separate `BarrowLib` build and import-boundary inspection check that no
foundation file imports a Newton-specific file. Cauchy completion remains
explicitly modern elementary infrastructure, with no derivative, integral
or ODE result used as a primitive. Counts and catalogue paths include both
library roots; this reorganization alone changes no completion score.

## Completed pairings and quadratic values, 5 October

PairingValues completes dot products and determinants of position values with
one Cauchy and representative-independence argument. It uses finite bilinear
difference identities, coordinate L1 bounds and boundedness on a proved
Cauchy tail. Globally Lipschitz SampledValues cannot complete these maps on
an unbounded plane. Reach for PairingValues for scalar products or directed
areas of completed points; use SampledValues for globally compared sampled
maps. Pairing outputs are scalar-coded values. Determinants are signed doubled
areas, and dot products define the Euclidean squared magnitude, distinct from
the L1 error gauge.

QuadraticPotentialValues constructs c*dot(p,p) and its normalized increment
between a completed endpoint and the tangent continuation. The finite
remainder bound uses the existing normalized second departure and explicit
finite point/velocity/departure bounds. It states no mechanical potential
relation. The Newton diagnostic ConstructedHarmonicPotential supplies that
relation by a finite work identity and actual node estimates. Its all-cell
leading potential result is the live client. Rational embedding compatibility,
the finite nonzero polynomial remainder control, Lean kernel reference checks
and all three library/default builds validate the construction; the rational
control is not an independent numerical oracle. No derivative, integral, ODE,
Newton-specific foundation import or historical edge is added.

TangentTriangleValues adds the signed doubled triangle of a completed point,
its tangent continuation and a completed next point. Reach for it for that
three-point geometry, rather than for area of a lobe or a matched region.
Rational embeddings agree with triangleTwice, and exact completed algebra
identifies its H^-3 normalization with half the determinant of velocity and
normalized second departure. PairingValues now transfers a closed bound in
one input under proved bounds on the other name's tail. The actual general
curve supplies its velocity cap and existing second-order bound, yielding
H*L*V² error for the normalized triangle. Shared completion, finite embedding
identities and all library/reference checks validate the construction; no
potential, area expansion or new historical premise enters the foundation.

CalibratedGrowth derives actual finite run bounds from the growth contract
|a(p)|<=L|p|+E, without supplied arrival bounds. Reach for it to compute state
and sampling caps; use BoundedIteration when arrival bounds are already known.
It reuses component amplification, finite powers and source budgets, and returns
a length cap M=2*(|x0|+tau|v0|+tau*T*E) on the calibrated window. Its time-unit
invariance and kernel-checked finite recurrence validate the output.
GeneralForceGrowth is the live Newton client: global comparison and centrality
derive growth, then all actual/coarse/shadow sample fields. This does not derive
region confinement or cover singular laws. No analytic primitive is added.

A.6 adds one shared positive-factor cancellation and one determinant/radial
lower-bound lemma to the existing arithmetic/triangle modules. The latter
returns r<=|p|_1 from r*V<=|det(p,v)| and |v|_1<=V, with V>0. The finite
RegionConfinement client keeps its central invariant and sampling order in
NewtonLimitDynamics; no force instance or new completed operation enters the
foundation. A zero-speed control rejects cancellation for a positive inner
radius. Kernel checks and all library builds validate the shared helpers.
