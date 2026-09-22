# Active proof obligations

This queue implements [the approved goals](GOALS.md). A checked finite
diagnostic is not completion of the corresponding historical proposition.

**Priority case (user instruction): zero force and rectilinear motion.**
ZeroForce.lean now derives the inertial map, unchanged velocity, exact
cross-denominator subdivision agreement, restart, rest and within-cell
positions from the constructed recurrence. Its zero-area timing example uses
different initial velocities, not nonuniqueness for fixed data. See ZERO_FORCE.md.
InertialControl.lean now supplies an explicit positive time radius controlling
both coordinates of inertial displacement, uniformly in rational base time,
including actual zero-force cells. InertialDefect.lean proves signed finite
defect cancellation for arbitrary closed inertial walks. Next make the extension
beyond rational times precise before claiming a complete inertial case.
Then continue the nonzero-force within-cell extension below.

Current progress: the bounded source map (1) is recorded in SECTION_II.md,
with unresolved De Motu counterparts explicitly retained. The equal-cell
finite recurrence now satisfies restart and contact (2), including the
constructed lattice velocity-jump law. A one-cell closed strip between
spatially compatible coarse/fine polygons is now exact finite triangle
algebra. The bounded rational common-force/time comparison (3) now derives
an endpoint mismatch `h*k*a` under an explicit end-kick convention, with equal
terminal velocities. Thus general refinement must allow controlled non-nested
endpoints; compatibility is not assumed. See TIME_SUBDIVISION.md. No
continuous-time realization is inferred. Finite arbitrary-partition formulas
and the exact residual/mesh coefficient bound now follow from the actual
end-kick recurrence in PartitionControl.lean; see PARTITION_CONTROL.md.

| Order | Obligation | Acceptance criterion |
| --- | --- | --- |
| 1 | Stage-local I–IV source map | Exact passages and supported dependencies for 1687/1713; De Motu counterparts qualified witness by witness |
| 2 | Finite contact and restart | Contact of actual recursively constructed cells, with any velocity jump derived from the displayed impulse; restart from the matching state |
| 3 | Time subdivision | Constant-force rational-time part closed: two-cell mismatch; endpoint and within-cell residual/mesh bounds (PartitionControl, PartialCell); an explicit small-residual refinement per tolerance (UniformRefinement); exact position/velocity comparison and packaged gap `partition_gap` for arbitrary partitions at a common rational time (PartitionComparison). Still open: absolute polygon-strip defect sums (kept separate from signed cancellation), extension beyond rational times, varying force |
| 4 | Proposition I realization | Identify the precise permitted premises that give a curve and the required area-time law; prove or isolate each implication |
| 5 | Proposition II converse | Finite Case-1 step checked (Converse.lean): equal oriented areas ⇔ deflection cC parallel to SB; rational central kick when B≠S; counterexamples for unsigned areas, vertex at S, and the undetermined sense. Case 2 finite step (uniformly moving centre) also checked. Next: unequal time cells, and the vanishing-triangle passage from a given realized curve |
| 6 | Proposition III relative motion | Derive relative-force composition from each edition's stated laws and corollaries; state admissible moving-center data |
| 7 | Proposition IV circular comparison | Construct required circle geometry and ratios with positive radii/time denominators, then justify the force interpretation |
| 8 | Boundary/action diagnostic (candidates in `action-arguments/`; none yet supports a universal constant) | For a substantive unresolved implication, derive a candidate residual and its dimension or produce a counterexample to the candidate; do not assume a universal constant |

For obligations 4–7, report a proved special case separately from the whole
proposition. If a historical premise cannot be recovered, continue independent
obligations while retaining that gap. A source-map entry is not a Lean theorem.

Validation is sequential and delegated. The final verification agent runs both
build targets and source/reference checks after implementation agents finish.
Use the formal-result ledger for actual theorem premises and the research state
for current completion boundaries. No task is marked complete solely because
a structure contains a field asserting its desired conclusion.
