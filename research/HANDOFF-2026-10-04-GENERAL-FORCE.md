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
   partition stability, system independence, rescaling freedom. Relate it to
   Arg004, which already finds phase area and the areal product as actions.
3. With a definition fixed, prove the area bound for the constructed curve in
   class (a), then wherever the other classes allow.

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

## Order

1. Task D.1: the inventory and boundary rule (short).
2. Task A: the general force interface and the class (a) and (b) estimates,
   with the harmonic field and the (∞) case as instances.
3. Task D.2: the migration.
4. Task B.1 and B.2.
5. Task C.1 and C.2. The exact finite-cell identities of C.2 can run
   alongside step 2.
6. Task B.3 and C.3.
7. Classes (c) and (d).

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
