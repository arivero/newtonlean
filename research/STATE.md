# Research state

Resume context: start from the [latest handoff](HANDOFF-2026-09-22-NEXT.md)
(end of the 22 September Claude Code session). The earlier
[22 September handoff](HANDOFF-2026-09-22.md) records the user's defect-area
correction. Its bounded common-time/force comparison
is now recorded in [time subdivision](TIME_SUBDIVISION.md); follow the next
obligation there and in TASKS.md rather than repeating the original task.
Continued autonomous work across the programme is authorized; see
[completion criteria](CONTINUATION.md).

Latest priority (3 October user instruction): **Proposition I, then II, III,
IV, in De Motu, 1687 and 1713 separately**. Construct the trajectory in the
primary forward variant. Its main area lies BETWEEN polygon and trajectory,
distinct from the Kepler area law. See [path defect](PROP_I_PATH_DEFECT.md)
and the [overnight checkpoint](OVERNIGHT-2026-10-03.md). Zero-force support
remains useful. The first finite suite
is implemented in `Polygon/ZeroForce.lean`: actual-cell and finite-schedule
agreement with `p+t*v`, constant velocity, cross-denominator subdivision
independence, exact restart, rest and within-cell positions. A zero-defect
example distinguishes motions with different initial velocities; it is not
fixed-data nonuniqueness. See [zero force](ZERO_FORCE.md). These are rational-time
constructions with no presumed limiting curve; full Euclidean-time realization
and additional geometric/area obligations remain separate.
`Polygon/InertialControl.lean` adds the explicit small-time bound: each positive
rational tolerance has a constructed positive radius that controls both drift
coordinates uniformly in position and rational base time, including an actual
zero-force cell. This closes the pending inertial estimate.
`Polygon/InertialDefect.lean` adds signed defect cancellation: directed
determinants of inertial samples compose additively, so every finite closed
walk (explicit connector included, sample times unordered) has zero signed
doubled area, and four actual zero-force schedules with arbitrary partitions
give a vanishing boundary. Unsigned enclosure estimates and extension beyond
rational times remain open.

Action diagnostic: candidate arguments now live in
[action-arguments](action-arguments/README.md), one file per proposer and
version. Arg001 records that every checked refinement residual vanishes with
the mesh. Arg002 records that Proposition IV Cor. 1 (1713 Cor. 7 for the
family) singles out inverse-cube circles as the one power law with a common
areal velocity, checked for two circles in `Diagnostic/InverseCubeAreal.lean`.
That action is system-dependent. At the user's direction the ledger now
develops arguments *for* a nonzero constant from the Latin and Newton's
revisions. Arg004 finds that the construction's exact invariants that survive
every mesh and every force (phase area, checked in `Diagnostic/PhaseArea.lean`,
and the areal product) are actions. Arg005 traces the short-time law from
hypothesis to the 1713 force clause (finite enclosure in
`Polygon/MonotoneEnclosure.lean`). Arg006 reads the two 1713 finiteness
clauses as a bound on one local action. None fixes a value.

Order 3's constant-force rational-time position/velocity comparison is closed by
`partition_gap`; absolute polygon-strip sums remain open. Order 5
has its finite Case-1 step in `Polygon/Converse.lean`: equal oriented areas
are equivalent to a deflection parallel to the radius, with orientation, a
vertex distinct from S, and the inward sense kept as separate premises.

Order 6 (Proposition III) now has its finite step in
`Polygon/RelativeMotion.lean`, with the source map in
[Proposition III](PROP_III.md): two bodies advanced by one pair recursion, each
with its own deflection history. Corollary VI of the laws is
`corVI_relative` — any common deflection history leaves both relative
coordinates unchanged at every stage — and Law I is `lawI_uniform` — an
undeflected reference body is exactly the uniform `centreAt` motion of its
initial pair. The compositional content of the proposition is
`relative_deflection_difference`: the relative polygon's deflection is `d n − e n`.
Equal relative oriented areas make that difference parallel to the relative
radius (`relative_equal_area_central`, and `relative_rational_central` with a
nonzero radius), which is also reachable by Newton's own route through
`Converse.moving_centre_equal_areas_central` (`propIII_via_moving_centre`).
That route now explicitly adds `−e` to both histories, identifies the reduced
reference body's `.p` at time `n` and `.q` at time `n+1`, and transfers the
original relative-area hypothesis before applying Proposition II.
The six Proposition III dependency edges (Corollary VI, Law I, Proposition II,
both editions) now carry these formal references. The limiting passage from a
realized relative orbit, parallelogram composition of simultaneous forces, and
any force/mass interpretation remain open.

Order 4 is decomposed in [Proposition I realization](PROP_I_REALIZATION.md).
`CentralSchedule.lean` proves the finite area law for any central field with
unequal rational cells and gives the exact refinement identities for a varying
force. The missing premise for the ultimate curve is control of force
differences; Proposition I cites none, and Lemma X's force qualification
(1687 *regularis*, 1713 *finita … continuo augetur vel diminuatur*) is the
nearest same-stage candidate. For the harmonic field (Prop. IV Cor. 3 case),
`HarmonicStability.lean` proves an exact equal-cell invariant and
mesh-uniform bounds on speed and position: the first stability result for a
varying central force. Convergence remains open.

The approved governing target is now the three-stage formalization of
De Motu, 1687 and 1713 arguments corresponding to Book I, Section II,
Propositions I–IV: see [goals](GOALS.md). M1–M4 below are supporting work.
The first new obligation is finite joining versus trajectory realization;
the action-constant hypothesis remains separate and unproved.

New finite diagnostic: `Polygon/Contact.lean` now compiles with explicit
position/velocity/impulse contact, restriction of supplied samples, and finite
gluing results. `motion_restart` proves exact continuation from the current
vertex pair with shifted impulses. The lattice construction derives the
velocity jump and zero-impulse velocity contact, rather than assuming them.
Its counterexample gives equal swept sums and unequal next vertices under
two different inward impulse histories (-1 and -2). It establishes insufficiency
of area data for identification, not failure of existence or fixed-force
uniqueness. Continuous-time refinement and mechanical realization remain open.

New finite refinement diagnostic: `Polygon/RefinementStrip.lean` constructs
the closed area between a coarse lattice edge and a spatially compatible
two-edge fine polygon. Its determinant identity reduces that signed doubled
strip to the Euclidean triangle on the three vertices; its `Nat` defect is zero
exactly when that signed strip is zero. The compatibility condition compares
finite `motion` endpoints explicitly, and the inward example has a nonzero
strip. This is not a swept-sector claim, a common-force time-refinement law,
or a limiting-curve construction.

The new rational `Polygon/TimeSubdivision.lean` comparison makes common
initial position, velocity, constant accelerative force and positive time
subdivision explicit. Under an end-of-cell impulse convention, the fine
endpoint equals the coarse endpoint plus `h*k*a`, while terminal velocities
agree. Exact nesting therefore fails in the constructed nonzero-force example.
An explicit straight connector closes the finite polygon comparison; it is
not a further mechanical cell. This is a modern constant-force diagnostic,
not Newton's general central-force theorem.

`Polygon/PartitionControl.lean` now connects arbitrary finite common-denominator
end-kick schedules to exact velocity and position formulas. It proves
`2*A+Q=T²` and `Q≤M*T`, with `Q` the sum of squared duration numerators and
`M` an upper bound on each. Against the explicitly constructed rational
polynomial map, the endpoint residual is exactly `(Q/(2D²))*a`; its scalar
coefficient is bounded by half the largest-cell bound times elapsed time.
See [finite partition control](PARTITION_CONTROL.md).
`Polygon/PartialCell.lean` adds within-cell positions: a partial final cell
`u/D` drifted from the actual prefix state has exact residual
`((Q+u*u)/(2D²))*a`, with `Q+u*u≤M*(T+u)` when `u≤w≤M`. The next step is
rational-time convergence to that map across partitions;
`UniformRefinement.lean` already gives, per positive rational tolerance, an
explicit refinement with residual coefficient below it, and
`PartitionComparison.lean` proves that two arbitrary partitions reaching one
rational time agree once each is corrected by its own exact residual,
retaining absolute defect accounting and the general central-force existence
obligation separately.

The [Section II source map](SECTION_II.md) now identifies printed I–IV
dependencies and De Motu antecedents for I and IV. Counterparts of II/III
were not found in the inspected De Motu ranges; this is not an edition-wide
absence claim. Proposition IV's explicit route differs between 1687
(Proposition II, Lemmas V/XI) and 1713 (Proposition II, Proposition I corollaries
2/4, Lemma VII). See the [ordered obligations](TASKS.md) for continuation.

The implementation request authorizes M1–M4 beyond the earlier M1-only boundary.
Scope stays within the requested changing proof architecture. Lean 4.19.0,
core/Std only; external dependencies remain empty.

| Milestone | Checked progress | Remaining completion barrier |
| --- | --- | --- |
| M1 | Independent H4 edited witness; rational consistency model; constructed s/t² and triangle normalization; conditional bridge and force-coefficient algebra; TEI/page-anchor collation | Direct image inspection and earliest H4 chronology; curved contact construction; mechanical velocity-area enclosure; variable-force corollaries |
| M2 | Constructed finite polygon, equal-area sums, maximum-width rectangle bound, conditional sector-ratio transfer | Geometric refinement connecting the constructed polygon family to an enclosed curve; continuous-force trajectory identification is a separate open issue |
| M3 | Conditional contact/cubic inequalities, finite sums, rectangle-derived 1/2 and 1/3 coefficients, reciprocal error convergence, rational uniform N^-2 bound | General curved contact geometry and mechanical identification of the velocity-area construction |
| M4 | C44 identity; evidence-qualified proposed outline; actual-edition DAGs and generated comparison; matched constant-force route algebra; TEI/page-anchor collation including 1726 views | Direct C42 and draft-folio/image collation; general generated/sagitta limiting comparison |

**M1–M4 are not certified complete.** Compiling conditional theorems and four
reports do not discharge their displayed geometric and historical premises.
See M1.md through M4.md and formal-results.json for exact boundaries.

Sources: TEI is the machine-readable authority; identifying translations and
untranslated passages are labelled. The source-collation report records page
and facsimile targets without downloading or reading manuscript images.
Selected PDF passages were visually checked; no general manuscript-image audit
is claimed. See [collation](collation.md) and edition-comparison.md.

Validation commands are in README.md. No sorry or project axioms were added;
standard Lean logical axioms can appear in generated dependency inspection.

Unrelated conversation-export deletion/new file remain untouched. No mathlib,
cache download, toolchain upgrade, correspondence or publication was performed.

## 2026-09-28 session (arena branch, toolchain built from source; continuation)
Resumed from `f50ff14` and extended the formalisation; all Lean compiles under
the source-built Lean 4.19.0 (core/Std only, no mathlib), both build targets, and
`research/CheckReferences.lean` elaborates every reference with axiom set
`{Classical.choice, Quot.sound, propext}` and no `sorryAx`.
- Order 6 (Proposition III, two-body): `Polygon/RelativeMotion.lean` proves
  relative deflection `d n − e n`, invariance under a common added history,
  uniform reference motion under zero deflection, and the finite relative-area
  converse. No `RelativeTwoBody.lean` module or Law III theorem is present.
  No mass/force law/limit is derived.
- Order 3 (time subdivision): `Polygon/StripArea.lean` proves signed sums —
  every two-cell chord triangle has signed doubled area `h^3*det(v,a)`, equal
  for all cells, so the signed total is `k*h^3*det(v,a)`. This does not prove an
  absolute-area sum; that obligation and a geometric strip decomposition remain
  open.
- Order 7 (Proposition IV): `Comparison/CircleCompare.lean` carries the exact
  finite sagitta-chord relation as a premise and proves equal-time
  `forceBySagitta` ratios proportional to the sagittae;
  per-edition limiting routes recorded, not derived (editions kept separate).
- Dependency graphs: `scripts/plot_graphs.py` renders the module and
  passage/reference dependency graphs to `docs/graphs/*.png`; see
  `research/figures.md`.
Open: order 4 (P3 convergence — needs a Fraction Cauchy-Schwarz/triangle
inequality, which the raw `equiv` relation makes non-trivial), order 8
(Arg004-Arg006), absolute polygon-strip sums, and the limiting routes/ODE
interpretation for Props III/IV.

## 1 October 2026 merge corrections

The Proposition III moving-centre theorem now derives the original relative
conclusion through Corollary VI, Law I and Proposition II with aligned vertex
times. Absolute strip-area completion has been withdrawn; the signed identity
remains checked. The absent-module claims were removed, and SVG/PNG/PDF
figures now preserve evidence status and legends. Both Lean 4.19.0 builds and
all 245 generated reference/axiom checks pass. See
[the verification record](VERIFICATION.md#merge-corrections-verified-on-1-october-2026).
