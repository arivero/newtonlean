# Handoff, 4 October 2026: general central forces and the polygon–curve defect

Written by Claude Code at the user's request, after commits `507d041` and
`39b0c0d`. The user authorizes the current working agent to attempt the tasks
below. Read [AGENTS.md](../AGENTS.md) and [GOALS.md](GOALS.md) first: stage
separation (De Motu, 1687, 1713), source-first edges, Lean 4.19 core only with
no mathlib, no `sorry`, both build targets, sequential v6 subagents and the
separate action-hypothesis layer all apply unchanged.

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

- **Whole plane: a required repair, first in order.** `LipschitzOn` is
  stated on `o.region`, but `Conditions.global_region : ∀ p, o.region p` (and
  `GeneralForceGrowth.Data`) make every general theorem a whole-plane
  theorem; the only instance built, the harmonic one, discharges it with
  `True.intro`. Nothing proves that the polygons stay in a region. A force
  Lipschitz on the whole plane is outside Newton's expectations: Proposition I
  concerns a force toward a point, and every law he applies it to (`1/r²`
  above all) is singular at that point. The whole-plane results therefore do
  not instantiate to the historical target; they are conditional diagnostics
  until A.6 is done. Do not build on `global_region` again, and re-derive the
  existing general theorems on the region premise rather than keeping two
  versions.
- **Proposition I's own conclusion.** No theorem states the area law for the
  constructed curve. Task E below adds it.

A code review of the 1,476 theorems found no loop (statement shapes repeat at
about 5 %, and the new theorems are used downstream) but a tower: each new
completed quantity rebuilds the same five-step kit, and all of it rests on the
`Conditions` bundle. Task D.4 addresses the kit.

## Task A — general force classes (main goal)

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

1. **Differential form.** For the constructed curve `γ` with its identified
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

Order from 5 October:

1. Finish and commit the current increment (`GeneralForceGrowth`: sample
   bounds derived from force data), without extending it.
2. Task A.6, required: region confinement replacing `global_region`
   everywhere; the ball case, then the annulus from the areal product, with
   Kepler's `1/r²` as the instance that must go through. Nothing else is to
   be started before this is committed.
3. Task E.1: the areal product constant along the curve.
4. Task C.1 and C.3: the between-path region's definition and vanishing.
5. Task E.2 and E.3: the sector area proportional to time, and the three
   edition wrappers.
6. Gluing of windows and partition independence.
7. Classes (c) and (d). Task D.4 applies from step 3 on: no new completed
   quantity without the generic lift.

Build downward before upward: no new layer on `Conditions` until A.6 and E
are in.

Commit each verified increment.

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
