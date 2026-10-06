# Handoff, 4 October 2026: general central forces and the polygon–curve defect

Written by Claude Code at the user's request, after commits `507d041` and
`39b0c0d`. The user authorizes the current working agent to attempt the tasks
below. Read [AGENTS.md](../AGENTS.md) and [GOALS.md](GOALS.md) first: stage
separation (De Motu, 1687, 1713), source-first edges, Lean 4.19 core only with
no mathlib, no `sorry`, both build targets, sequential v6 subagents and the
separate action-hypothesis layer all apply unchanged.

## Controlling user clarification, 6 October

Take the trajectory's existence as an explicit postulate in the primary
historical proof. In Lean, supply the curve as a parameter; retain its
mechanical laws and any regularity requirements as separately visible
premises. This supersedes the earlier requirement to construct a motion
before proving Proposition I. The completed constructions remain supporting
results and are preserved.

Keep the two areas distinct. (A) The goal of Proposition I is swept sector
area proportional to elapsed time, hence equal swept areas in equal times.
(B) The nonnegative area between Newton's impulse polygon and the given
trajectory is a reference for proving that his approximation approaches
the curve. Neither (A), (B), nor convergence/identification of the polygon
with the curve may be smuggled into the existence postulate. Equal swept
areas alone imply neither path agreement nor vanishing (B).

`SweptArea.Proportional` now names the given-trajectory curve-fan target;
`GeneralForceArea.proportional_swept_area` supplies the already proved
constructive instance. This adds no new existence or historical area proof.
The postulate is a user-authorized editorial convention, not an explicit
axiom attributed to Newton. See
[the checkpoint](verification/trajectory-postulate-2026-10-06.md).

## Where things stand

- 793 library theorems, 501 substantive by the heuristic in
  `scripts/progress_stats.py`. The Proposition I realization (TASKS.md order 4)
  holds 489 of them. 356 sit in the harmonic-specific modules (`Harmonic*`,
  `PositionValues`), built for `HarmonicStability.linearField w` under
  `SmallTime` / `DyadicSmallTime`, i.e. `T*(1+|w|) ≤ 1/2`: one force law on a
  short window. 133 sit in generic modules (`CentralSchedule`, `FiniteGrowth`,
  `CauchyValues`, `BinaryTime`, `PathDefect`, `PointBounds`, `TriangleBounds`,
  `ConvexCover`).
- General-field infrastructure already exists in `Polygon/CentralSchedule.lean`:
  `Field := Point → Point`, `central`, `cell`, `schedule`, `swept_eq` (finite
  area law for any central field, unequal rational cells), `refine_position`
  and `refine_velocity` (any field), `unequal_cells_converse`.
- The trajectory is constructed twice, and the user wants both kept:
  - (E) endpoint names, rescaling a whole schedule for each rational time:
    `HarmonicDyadic.endpointName`, `HarmonicTimeComparison.timeName`.
  - (G) prefixes of one global dyadic family: `HarmonicBinaryPrefix.prefixName`,
    `BinaryTime`, `HarmonicTimeRealization.gammaValue`,
    `PositionValues.gammaPosition`.
  Their agreement is unproved. Their geometric-tail lemmas are proved twice,
  once per construction, for different coefficient definitions.
- The polygon–curve links are at vertices only:
  `CauchyValues.constant_approximants_converge` (approximants converge to their
  realized value) and `CauchyValues.binaryValue_prefix_bound` (each level-`m`
  prefix vertex lies within `tailCap m` of its realized value). The edition files'
  `polygon_trajectory_defect_control` takes the area as an arbitrary function
  of the mesh with the enclosure as a hypothesis. No Lean definition of the
  polygon–curve area (D_mesh) exists. The P4 work (`ConvexCover`,
  `HarmonicCover`) bounds square covers between a polygon and its refinement.
- Exact cross-product formulas already exist on finite polygons:
  `HarmonicRefinement.closed_defect_cubic` (closed signed doubled defect
  `-h^3*w*det(x,v)` for one refinement) and, for the constant force,
  `StripArea.two_cell_triangle_constant` with `all_triangles_equal` (every
  triangle of consecutive vertices has doubled area `h^3*det(v,a)`).
- Shared helpers (since `507d041`): generic fraction lemmas in
  `Common/RationalMagnitudes.lean` (`Fraction.add_equiv`, `mul_equiv`,
  `add_equiv_left`, `mul_equiv_right`, `le_add_nonnegative`,
  `nonnegative_add`, `nonnegative_mul`, `add_zero`, `mul_zero`, `add_mul`, ...);
  point lemmas in `TimeSubdivision` (`pointEquiv_symm`, `pointEquiv_trans`,
  `pointAdd_congr`, `pointScale_congr`, `det_add_right`); state-norm component
  bounds in `PointBounds`. Search these before writing a helper and put new
  generic helpers there, never as private per-file copies. When two
  constructions need the same estimate for different constants, prove it once
  with the constant as a parameter.

## Update, 5 October, after commit caff2aa

Done since the handoff: the BarrowLib migration; the sampled-force interface
(`ForceClasses.Oracle`, classes A–D, the parallel field); general finite
estimates and accumulation; calibrated time units; general endpoint values,
prefix curve, E/G agreement at every dyadic time, whole-edge bounds; the
polygon–curve region with outer content decreasing like `4C²/2^m`; velocity
and force identified through secants; the deflection-triangle and
potential-step limits; Arg007. The harmonic field is an instance throughout.
`GeneralForceGrowth` derives the sample bounds of `Conditions` from the
Lipschitz contract and the window; it is committed as `a688803`. The first
finite A.6 increment derives ball/annulus membership before each force sample,
including both shadow arrivals. Construction/completed-force localization and
the actual Euclidean Kepler instance remain required; A.6 is not complete.

Two gaps remain, and they come before any new completed quantity:

- **Whole plane: a required applicability repair.** `LipschitzOn` is
  stated on `o.region`, but `Conditions.global_region : ∀ p, o.region p` (and
  `GeneralForceGrowth.Data`) make every general theorem a whole-plane
  theorem; the only instance built, the harmonic one, discharges it with
  `True.intro`. Nothing proves that the polygons stay in a region. A force
  Lipschitz on the whole plane is outside Newton's expectations: Proposition I
  concerns a force toward a point, and every law he applies it to (`1/r²`
  above all) is singular at that point. The whole-plane results therefore do
  not instantiate to the historical target; they are conditional diagnostics
  until A.6 is done. The regional interface repair is now committed; remaining
  A.6 work and the Kepler instance follow the general Proposition I proof,
  as the user clarified on 5 October evening. Do not build on `global_region`
  again, and re-derive the
  existing general theorems on the region premise rather than keeping two
  versions.
- **Proposition I's own conclusion.** No theorem states the area law for the
  constructed curve. Task E below adds it.

A code review of the 1,476 theorems found no loop (statement shapes repeat at
about 5 %, and the new theorems are used downstream) but a tower: each new
completed quantity rebuilds the same five-step kit, and all of it rests on the
`Conditions` bundle. Task D.4 addresses the kit.

## Task A — general force classes and subsequent applicability

The user's 5 October evening clarification controls the order: prove the
general Proposition I construction and swept-area conclusion first. A.6 and
force-specific instances follow that proof. Retain the regional repair already
committed, but add no independent force proof ahead of the general proposition.

Generalise the realization chain to an arbitrary central force, as
Proposition I states it: force directed toward one fixed point S, of any
magnitude. The only permitted extension is moving S to infinity (uniform
parallel force, the Galilean parabola). Non-central forces, the later
nineteenth-century generalisations, are out of scope. The harmonic field
becomes one instance: re-derive the existing harmonic results as corollaries
and keep their names working.

The goal is the general law; individual laws are tests of it. A law the
current setup cannot express is part of the generalisation problem. For
example, `r = √(x·x)` is in general irrational at rational points, so a
rational-valued `Field` cannot carry an arbitrary magnitude law `f(r)`. Design
the force interface so that every law in the classes below fits, for instance
with force values in a completed planar type built like `CauchyValues.Value`
and `PositionValues.PositionValue`, or as rational approximations `a_n` with
explicit uniform error carried through every estimate. Choose, justify and
document the design before building on it.

The user's classes are regularity classes of the magnitude law, all directed
toward S:

- **(a) conservative central:** magnitude depends only on distance and is
  Lipschitz on the region of motion; a potential exists.
- **(b) central, continuous, non-conservative:** magnitude depends on
  direction as well as distance, `F(θ, r)` continuous.
- **(c) distance-only magnitude, merely continuous:** no Lipschitz bound. Such
  laws still have a potential, so (c) differs from (a) by regularity: treat
  existence of a limit and its uniqueness separately (Peano-type examples such
  as `f ∝ √|r - r₀|`).
- **(d) no continuity:** arbitrary dependence `F(θ, r)`, discontinuous or
  "random". The finite area law survives (`swept_eq` needs only `central`).
  Expect convergence or uniqueness to fail and construct explicit
  counterexamples.
- **(∞) centre at infinity:** the uniform parallel field. Connect it to the
  existing constant-force results (`TimeSubdivision`, `PartitionControl`,
  `PartitionComparison`) and state what equal areas become: uniform motion of
  the velocity component perpendicular to the force.

Technical guidance (verify each point; none is a premise):

- The harmonic estimates appear to use only a Lipschitz bound
  `|a(x)-a(y)| ≤ L|x-y|` on a region, a growth or boundedness bound, and
  confinement of the polygons to that region. Replace `|w|` by `L` and the
  smallness condition by its `L` analogue.
- Laws singular at S need an annulus `r ≥ r₀ > 0`. Derive confinement where
  the class allows (energy, angular momentum) or name it as an explicit
  premise. Arg003 records why the inverse cube marks this boundary.
- **A.6, region instead of whole plane (added 5 October).** Remove
  `global_region` from `Conditions` and `GeneralForceGrowth.Data`. In its
  place take a region `R` with `LipschitzOn` and the sample bound on `R`, and
  a *confinement* proof that every point at which the construction samples
  the force lies in `R`: polygon vertices at every level, coarse vertices,
  shadow arrivals, and, in the completed layer, the curve points. Derive
  confinement rather than assume it:
  - For laws regular at the origin, `R` is the ball of radius
    `|x₀| + T·V` about the origin, where `V` is the velocity cap; every
    vertex within the window lies in it, so a Lipschitz bound on that ball
    suffices. Class (a) then genuinely means locally Lipschitz.
  - For singular laws, `R` is an annulus `r₀ ≤ r ≤ R₀`. A lower bound on the
    radius comes from Proposition I's own finite content: the areal product
    `det(x, v) = ℓ` is exactly constant along every polygon
    (`CentralSchedule.schedule_momentum`), and `|det(x,v)| ≤ |x|₁ |v|₁`, so
    every vertex has `|x|₁ ≥ ℓ / V`. With `V = |v₀| + T·B(r₀)` this is a
    condition on `T` that gives `|x|₁ ≥ r₀` throughout the window; check that
    the shadow arrivals and curve points obey the same bound. The outer radius
    comes from the ball above. This derivation is to be checked, and it is
    the test case for Kepler's `1/r²`, which must become an instance.
  - The harmonic instance keeps `R` = everything and must still go through.
- Keep units explicit. The Lipschitz constant `L` has units 1/time² and
  defines the local dynamical time `τ_L = 1/√L` (harmonic: `1/ω`; gravity
  near radius r: about `√(r³/GM)`); a mesh converges when `h ≪ τ_L`. Only the
  existence of a finite `L` on the region is assumed; its value depends on the
  law and the region and fixes no universal constant. The current conditions
  silently fix a unit of time: `T·(1+L) ≤ 1/2` adds 1 to a quantity of units
  1/time², and the state magnitude `|x|+|v|` adds a length to a velocity.
  Carry the calibration explicitly, for example `|x|+τ₀·|v|` with a window on
  `h²·L` and `h/τ₀`, and show the conclusions are invariant under rescaling
  the time unit. Newton's counterpart is qualitative finiteness (1713
  Lemma X *Vi finita*, Lemma XI *curvaturam finitam*); Arg006 reads it as a
  local scale.
- Extend beyond the short window by restarting and gluing windows
  (`motion_restart` in `Polygon/Contact.lean` and the ZeroForce restart
  results cover finite polygons). Prove continuity across each join.
- Proposition I covers any centripetal force. Relate the classes to the
  edition-local regularity clauses: 1687 Lemma X *vi regulari*, 1713 Lemma X
  *Vi finita … continuo augetur vel continuo diminuatur* (monotone magnitude,
  hence bounded variation; see PROP_I_REALIZATION.md). Importing either clause
  into Proposition I is `editorial_interpretation`; the Lipschitz class is
  `modern_reconstruction`. Keep the three stages separate.

## Task B — the two constructions and the curve

1. Prove that (E) and (G) agree at common times: a theorem relating `timeName`
   values to `gammaValue` at dyadic rational times. Keep both constructions.
2. Bound the distance from polygon to curve along whole edges, at every time
   inside a cell, explicitly in `h`.
3. Identify the constructed velocity with the rate of change of the
   constructed position (difference quotients converge), and acceleration
   with the sampled force: obligation P5, for each class where it holds.

## Task C — the polygon–curve defect as an action-like object

The user's aim for comparing polygon and curve: an area, built from a cross
product (hence an action once multiplied by mass and divided by time), that
is essentially proportional to `Δt·ΔV` for the potential energy `V`. Here
`ΔV = V(C) - V(c)`: the difference between the potential at the actual next
point C and at Newton's inertial continuation c = B + v·Δt along the tangent.
This `ΔV` is nonzero on a circular orbit even though `dV` along the orbit is
zero. Comparing a polygon with its refinement is progress toward this; the
target is the polygon–curve object itself.

1. Define D_mesh in Lean. Candidates, each named and catalogued as
   `modern_reconstruction`: the limit of lobe sums between the mesh polygon and
   its dyadic refinements; outer content as the infimum of square-cover
   budgets (ConvexCover and HarmonicCover are the ingredients); the per-cell
   closed-boundary determinant with lobes counted separately. For each, state
   how crossing lobes are counted without cancellation.
2. Derive the per-cell relation between these areas and `Δt·ΔV`, exactly on
   polygon cells and at leading order for curves. A derivation to check, never
   to assume. With step `h`, `Bc = v·h` and deflection `cC = a·h²` (kick
   convention):
   - Deflection triangle: `Area(B,c,C) = ½·h³·|v×a|`.
   - Potential step: `ΔV = V(C) - V(c) ≈ -F·cC = -m·|a|²·h²`.
   - Hence `m·Area = τ·Δt·|ΔV|` with `τ = v⊥/(2|a|)`, where `v⊥` is the
     velocity component perpendicular to the force. `τ` is a time.
   - Galilean fall (V = m·g·y): `τ = v₀/(2g)`, exact on every polygon cell and
     constant along the whole parabola, since `v₀` is the constant horizontal
     speed. This is the user's proportionality in its cleanest form. The area
     half is already checked: the triangle of consecutive vertices A, B, C has
     the same area as B, c, C, and `StripArea.two_cell_triangle_constant`
     gives its doubled area `h³·det(v,a)` on every cell.
   - Circular orbit, any law: `τ = r/(2v)`, constant.
   - General central orbit: `τ = L/(2·r·|f(r)|)` with `L` the angular
     momentum. It is constant along non-circular orbits exactly when
     `r·f(r)` is constant, i.e. `f ∝ 1/r`.
   - Consistency check: in the plane, `Δt·(Δx×F)` has the form `Δt·ΔW` for a
     local potential `W` exactly when `div F = 0`. Among distance-only central
     laws this also singles out `f ∝ 1/r`, and then `W` is a multiple of the
     polar angle, multivalued around S; with angle dependence, `c(θ)/r`
     qualifies.
   - The chord–arc lobe `(v×a)·h³/12` and the D_mesh lobes have the same
     cross structure with other constants; the harmonic formula
     `-h³·w·det(x,v)` already shows it.
   Prove the exact finite identities first where arithmetic allows (Galilean
   and harmonic potentials, both polynomial), then the leading-order
   statement for class (a). Confirm, correct or refute each bullet.
   Record the outcome as a new action argument in
   [action-arguments](action-arguments/README.md) (next Arg number, proposer
   tag per its README) with the GOALS.md tests: positivity, finiteness,
   partition stability, system independence, rescaling freedom. A scale read
   off the estimates that changes with the time-unit calibration `τ₀` is an
   artifact of the hidden unit, not a property of the motion. Relate it to
   Arg004, which already finds phase area and the areal product as actions.
3. With a definition fixed, prove the area bound for the constructed curve in
   class (a), then wherever the other classes allow.

## Task E — Proposition I's own conclusion on the constructed curve (added 5 October)

The theorem Newton states is that the constructed motion sweeps areas
proportional to the times, in one plane. Nothing yet says this about the
curve; the finite law `swept_eq` is exact on every polygon, and the three
edition files only carry the conditional interface
`polygon_trajectory_defect_control`, whose enclosure is a hypothesis.

1. **Supporting differential form.** This is the areal product, not the
   polygon–curve remnant and not the full Proposition I conclusion. For the
   constructed curve `γ` with its identified
   velocity `v` (Task B.3), prove that the areal product `γ(t) × v(t)` is
   constant in the value space: `pairingValue detForm (γ t) (v t) =
   pairingValue detForm (γ 0) (v 0)`. The proof passes `schedule_momentum`
   through the vertex convergence (`binaryValue_prefix_bound`) and the
   velocity secants; `PairingValues.detForm` already lifts `det`.
2. **Newton's form.** Define the swept area of the curve up to time `t` as
   the limit, along the dyadic levels, of the polygon fan sums `swept`. By
   `swept_eq` every level gives exactly `ℓ·t/2`, so the limit is immediate;
   the content is that this limit is the area of the sector `S γ(0) γ(t)`:
   the sector and the polygon fan differ by the between-path region, whose
   content vanishes (Task C.3, or the winding-number definition of C.1). State
   the theorem as "sector area = `ℓ·t/2`", that is, proportional to the time.
3. **Edition wrappers.** Derive, in `Principia1687/PropositionI`,
   `Principia1713/PropositionI` and `DeMotu1684/AreaLaw`, the realized theorem
   for each stage from the construction, discharging the enclosure hypothesis
   of `polygon_trajectory_defect_control` instead of assuming it, and keeping
   the stage-local passage citations and classifications. Planarity is built
   into the planar model; say so in the docstring rather than claim it as a
   result.
4. Update PROP_I_REALIZATION.md's obligation table (P3–P5) and the completion
   estimate only with the theorems named.

## Task D — a period-appropriate foundation library (subsidiary)

The user excludes mathlib for two reasons: its size (disk space and
compilation time) and its post-Newtonian content. As far as we know, no
pre-integral-calculus subset of mathlib exists as a separate package.
Importing only selected mathlib modules would keep later theorems out of
scope, but the whole package would still have to be downloaded, then compiled
or fetched as a large prebuilt cache. Instead, separate the project's own
generic mathematics into a foundation library, provisionally `BarrowLib`. Its
content stays within what Newton's contemporaries could cite (Euclid's
proportions, Archimedean exhaustion, Barrow-style ratio and tangent
arguments), plus explicitly marked modern elementary infrastructure: rational
arithmetic, finite sums, and Cauchy completion as the stand-in for ultimate
ratios. No theorem in it uses derivatives, integrals or ODE results as
primitives.

1. Inventory first. Classify each generic module and theorem as foundation or
   Newton-specific: `Common/*`, the point algebra in `TimeSubdivision`,
   `PointBounds`, `TriangleBounds`, `ConvexCover`, `FiniteGrowth`,
   `CauchyValues`, `BinaryTime`, and the generic part of the harmonic tail
   arithmetic. Record the boundary rule in a short note.
2. Migrate in one verified commit: a separate `lean_lib` in `lakefile.lean`
   that `NewtonLimitDynamics` imports. Regenerate `formal-results.json`,
   `CheckReferences.lean` and the `formal_refs` in `dependencies.json`, and add
   `lake build BarrowLib` to the AGENTS.md and README verification commands in
   the same commit. `scripts/catalogue_formal.py` and
   `scripts/progress_stats.py` scan only `NewtonLimitDynamics/`; extend both
   so the moved theorems stay catalogued and counted. Keep declaration names
   stable where possible; if namespaces change, update every reference.
3. Generic estimates produced by Task A (Lipschitz-field bounds, geometric
   tails with the coefficient as a parameter) belong in the foundation library
   from the start.
4. **One lifting kit (added 5 October).** `SecantValues`, `PairingValues`,
   `QuadraticPotentialValues`, `TangentTriangleValues` and `SampledValues`
   each repeat the same five steps for a new operation: finite distance
   bound, Cauchy name, equivalence invariance, quotient value, embedding
   identity. `mapValue` does this once for one-argument nonexpansive maps;
   `PairingValues.Form` is nearly the two-argument version. Write the generic
   two-argument lift (a bilinear or Lipschitz-on-bounded-sets operation with
   its bound as data) in BarrowLib and derive the existing operations from it;
   introduce no further completed quantity without it.

## Order

Original order: D.1, A, D.2, B.1–B.2, C.1–C.2, B.3 and C.3, classes (c)
and (d). Steps D.1, A (first pass), D.2, B.1–B.3 and C.2 are done.

Order clarified on 5 October evening and amended by the user on 6 October:

Completed before this clarification: `GeneralForceGrowth` and the general
regional construction repair. Preserve the verified regional premises and
derived polygon/coarse/shadow/curve confinement.

1. **Proposition I itself comes first:** take the central-force trajectory
   as given and prove that its swept areas are proportional to elapsed times,
   with separate De Motu, 1687 and 1713 wrappers. Task E.1's constant areal
   product is a supporting lemma, not the proposition. Tasks C.1/C.3 and
   E.2/E.3 must connect the given trajectory, intervening region and
   sector area. The existence constructions remain supporting results; the
   approximation to the given trajectory still needs proof. The evening
   review's item 1 supplied the first concrete construction step:
   ground the actual general `PolygonTrajectoryEnclosure` from the proved
   content decay; retained instances inherit the same general proof.
2. Only after that general given-trajectory proof is complete, finish A.6
   and instantiate the theorem for Kepler's `1/r²`. Force-specific work is an application of
   the general proof, not a substitute for it. The started Kepler work is held
   separately until this step.
3. Gluing of windows and partition independence.
4. Classes (c) and (d).

Task D.4 continues to apply: introduce no further completed quantity without
the shared generic lift. Commit verified increments, and distinguish every
supporting lemma from the full Proposition I conclusion.

## Current verified construction increment, 5 October evening

GeneralForceArea.constructed_area_law now gives intrinsic swept area of the
actual regional Lipschitz local curve, equal to |ell|*t/2, together with
vanishing actual intervening content. Oriented area is ell*t/2. E.1's areal
product is only support. Actual curve-node fans construct the area value;
no area limit or enclosure is a premise. The general and retained harmonic
content clients ground PolygonTrajectoryEnclosure, and D.4's BinaryLift is
shared by pairings, secants and fan addition. Separate stage/witness wrappers
are named modern reconstructions; planarity is built into the model and
unsigned fans count multiplicity.

The [proof route](PROP_I_REALIZATION.md#proof-dependencies-and-the-implementation-route)
was read from the Latin proof paragraphs and traced through the cited laws,
composition proofs and Lemmas I–III. Ordinary sector-union area, unrestricted
force identification, arbitrary partitions and historical limiting proof
certification remain open. These are part of the general target's scope;
Kepler work stays held until the general proof requirements are met.

## Interval extension and next dependencies, 6 October

`GeneralForceArea.constructed_interval_area_law` extends the same actual
local curve construction to unsigned fans between arbitrary BinaryTime
endpoints. Their area is `abs(ell)*abs(t1-t0)/2`, with address independence,
uniqueness, reversal and zero-length controls. The diagonal area name retains
actual curve-node fan approximants. The formula follows from their proved
geometric error; it is not the area's definition. Canonical finite and completed
interval fans compose by addition. All existing initial-time APIs remain.
No force instance or completion-score increase is added.

Latest user direction: after this patch, prove the results Proposition I
invokes, at least the Laws' Corollary 1 and Lemma III Corollary 4, following
their own proof dependencies. This is the next concrete work within Order 1,
before Kepler or another force-specific application. The printed editions
explicitly cite those results; De Motu's composition references and unnumbered
limiting passage stay witness-local. Source-map entries and conditional
interfaces do not certify the invoked proofs.

## Invoked composition proof increment, 6 October

The Laws' Corollary 1 has a checked finite rational reconstruction of its
proof: directed parallel impulse changes preserve transverse motion;
`uniform_endpoint_lines` derives the two endpoint constraints independently
of the diagonal theorem; elementary determinant coordinates prove their
unique intersection. Separate 1687/1713 and NATP00090 results use this route.
The uniform impulse model also covers parallel, opposite and zero impulses,
and `next_arrival_diagonal` proves that the actual central-force recurrence
uses the same composition. Mechanical Law I/II premises remain explicit in
the model, 1713's added wording stays local, and NATP00089's hypothesis is
not relabelled as a historically proved lemma. No completion score changes.

The next boundary increment proves the chord component behind Lemma III
Corollary 4: closed chord traces approach a given uniformly controlled curve
in both directions as the maximum cell span shrinks. Dyadic spans/coverage
are derived, including endpoints and zero windows. The actual general curve
derives its own modulus, and both its inscribed chords and its actual force
polygons have proved two-sided boundary limits. Separate printed-edition and
De Motu wrappers preserve source provenance. The preceding corollaries are
now traced through their proof connectives in the source graph; the tangent
inference is kept distinct from the chord proof.

The next supporting-line increment constructs a rational meeting from
opposite endpoint support inequalities and derives its endpoint rectangle.
It includes coincident lines, both support orientations and increasing or
decreasing patches. Independent line directions give unique intersection.
Every completed point of both joined segments inherits the finite bound;
uniformly convergent finite nodes on a given uniformly controlled curve then
give a two-sided boundary limit as the maximum cell span shrinks. Separate
1687/1713 Corollaries 3–4 wrappers retain the supplied finite line data and
curve modulus. Actual tangent identification and vertical tangent patches
remain separate. See verification/lemma3-supporting-boundaries-2026-10-06.md.

The following monotone-rectangle increment derives the actual lower/upper
rectangle sets around a fixed given rational graph, including all completed
closure points. Ordered partition coverage and represented endpoint transport
are proved. It constructs the largest actual width, proves the exact
equal-width rectangle-sum identity and unequal-width maximum-times-height
bound, then exhausts the derived gap as maximum widths shrink. Separate
1687/1713 wrappers preserve the source passages and modern geometric premises.
See verification/lemma2-3-monotone-rectangles-2026-10-06.md.

The conditional given-motion bridge below now supplies a swept-fan law from
explicit local consistency. Next derive that consistency from the given
trajectory's independent mechanical premises, without
rebuilding existence or assuming polygon/curve agreement. The separate
between-path control supports the limiting passage. In the invoked-lemma
chain, identify the finite rectangle side-product sums with ordinary
area of the rectangle unions and realize the given curvilinear figure's area
between them, before concluding the ultimate ratio by Lemma I with a
nonzero-area premise made explicit. Actual tangent
identification and vertical patches remain separate.
Neither trace convergence nor a scalar area budget proves arclength convergence.
No force instance or completion-score increase is added.

## Verification and reporting, every increment

- The README verification list, at least: `lake build`;
  `lake build NewtonLimitDynamics`;
  `python3 scripts/catalogue_formal.py`; `python3 scripts/check_graph.py`;
  `lake env lean research/CheckReferences.lean` (standard axioms only, no
  `sorryAx`); `python3 scripts/test_evidence_validation.py`; `git diff --check`.
- `python3 scripts/progress_stats.py`, then commit `docs/progress`. Judge
  progress by the substantive count; plumbing, number checks and duplicates
  are overhead. Change `docs/progress/completion-estimate.json` scores only
  with stated evidence.
- Update STATE.md, TASKS.md (order 4), PROP_I_REALIZATION.md,
  PROP_I_PATH_DEFECT.md, CAUCHY_REALIZATION.md and VERIFICATION.md. Correct
  outdated claims in place instead of appending qualifiers.
- A failed attempt, a counterexample or a refuted conjecture is a result:
  record the exact statement, its premises and the countermodel. Lean
  rejection alone proves no obstruction.
- Preserve the unrelated conversation-export files.

## Review findings on the Lean, 5 October evening

A full read of every module as printed in `docs/reference/principia-with-lean.md`
(report: [review-principia-with-lean-2026-10-05.md](review-principia-with-lean-2026-10-05.md))
found no `sorry`, axiom, non-structural recursion or circular definition, and
every quotient lift carries its invariance proof. What it found is softer and
goes on the queue, in this order:

1. **The limit layer is never grounded.** Every theorem concluding `Ultimate`,
   `Near`, `Vanishes` or `QuadraticInitialDeflection` has a hypothesis of the
   same kind; no unconditional instance exists. In particular
   `PolygonTrajectoryEnclosure` is never proved for any concrete pair, so the
   four edition theorems for Proposition I's last step stay conditional even
   for the harmonic field, where `HarmonicPathRegion.D_mesh_tends_zero`
   already holds but is not connected to `Vanishes`. This is Task E.2's first
   concrete step: derive `PolygonTrajectoryEnclosure` for the harmonic
   instance from `D_mesh_tends_zero`, then for the general regional
   construction.
2. **Premise bundles with no instance.** `Principia1687.LemmaXPremises`,
   `Principia1713.LemmaXPremises` and `ContactEnclosure` are bundles of limit
   fields whose theorems are their squeeze, never instantiated; the 1713
   structure only wraps the 1687 one, so the 1713 *Vi finita* clause has no
   formal content, while `MonotoneEnclosure` formalizes it on finite cells
   unconnected to the theorem. Either build instances from the finite
   results or rename these as interfaces in their docstrings and the
   catalogue notes.
3. **The force oracle is only ever exact.** `exactOracle`, `harmonicOracle` and
   `parallelOracle` all set `error := 0`; `error_vanishes` and `coherent` are
   never discharged. The Kepler `1/r²` instance of A.6 is the first real test;
   `GeneralForceGrowth.Data` is also never instantiated, and no annular
   `Frame` constructor exists although the docstring says singular laws use
   one.
4. **Vacuous or unused classes.** `ClassDForce := True`; `ClassBForce`,
   `ClassCForce`, `ContinuousOn`, `BoundedOn`, `CalibratedGrowth.Growth`
   appear only as hypotheses. Give class (d) honest content (finite centrality
   only) or remove it, and establish B/C for at least one oracle each when
   classes (c)–(d) are reached.
5. **Docstrings that overclaim.** `Comparison/CircleCompare`: `sagitta_chord`
   is used by no theorem and `force_ratio_is_sagitta_ratio` is
   cross-multiplication, yet the docstring calls them a checked core, and it
   attributes the sagitta-over-`t²` measure to Proposition II (it is Lemma X
   Cor. 2 / 1713 Prop. I Cor. 4). `ZeroForce.inertialAt` says it is built from
   the recurrence; it is the closed formula, with agreement proved afterwards.
6. **Housekeeping.** Dead declarations `Contact.Quantities`,
   `PartitionControl.positiveWeights`, `SeqVanishes`; one file declaring into
   six namespaces (`BarrowLib/Polygon/DyadicArithmetic`, also `PointAlgebra`,
   `StateDistance`), which hides where names live; `decide` on large nested
   rationals in four sample theorems. Catalogue anchors to revisit:
   `Contact/FiniteSums` is Lemma II–III material anchored to Lemma XI, and
   `HarmonicStability` serves Proposition I but is anchored to Prop. IV Cor. 3.

Items 1 and 3 are part of Tasks E and A.6; items 2, 4 and 5 are small and can
be done when their modules are next touched; item 6 is housekeeping for a
quiet moment. None changes a completion score.

## Given-motion consistency bridge, 6 October

[The consistency checkpoint](verification/given-trajectory-consistency-2026-10-06.md)
now proves a conditional theorem for an independently supplied state curve.
Finite stability accumulates its rational samples' one-cell mechanical
residuals; a shrinking scalar local-source budget and representation of the
supplied curve then prove equality with the retained polygon limit. The
all-interval swept-fan law follows, and the actual matched-region outer
content tends to zero in a separate theorem. Neither agreement nor either
area conclusion is assumed. Local consistency is an additional explicit
premise, not part of trajectory existence. Deriving it from independently
stated motion laws, identifying ordinary swept-sector area and certifying
Newton's stage-local limiting proofs remain open. This adds no historical
completion credit and does not release force-specific applications.

Next within Order 1: derive the local cell residual and its shrinking rate
from separately stated motion laws and regularity, rather than defining a
physical trajectory by the polygon limit. Preserve the independence of the
curve's own rational representation. Ordinary sector-area identification and
the invoked Lemmas II–III area passage remain open. No new historical wrapper
is added for the conditional consistency theorem.

## Refactor requested after the consistency increment, 6 October

The user asks to consider a main library with exactly one historical theorem,
lemma, law or corollary per file, containing its exact Latin and corresponding
formal definitions/proof. Supporting material is to be organized in BarrowLib,
ClassicsLib and ModernLib according to mathematical content. The concrete
inventory, source policy and proposed migration order are in
[HISTORICAL_FILE_REFACTOR.md](HISTORICAL_FILE_REFACTOR.md).
This is a design record; the migration has not yet been performed. The
user selected one file per historical result, with separate edition sections
containing each witness's own Latin, definitions, proof and dependency record.
Existing proof status and the separation of editions remain unchanged.
