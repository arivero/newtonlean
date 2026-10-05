# Active proof obligations

This queue implements [the approved goals](GOALS.md). A checked finite
diagnostic is not completion of the corresponding historical proposition.

**Priority (3 October user instruction): Proposition I, then II, III, IV,
in De Motu, 1687 and 1713 separately.** The primary forward variant constructs
the trajectory. Its main polygon–trajectory area is distinct from the Kepler
area; supplied-curve enclosures are diagnostics. See PROP_I_PATH_DEFECT.md.

Earlier priority case: zero force and rectilinear motion.
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
| 3 | Time subdivision | Constant-force rational-time part closed: two-cell mismatch; endpoint and within-cell residual/mesh bounds (PartitionControl, PartialCell); an explicit small-residual refinement per tolerance (UniformRefinement); exact position/velocity comparison and packaged gap `partition_gap` for arbitrary partitions at a common rational time (PartitionComparison). Signed two-cell triangle sums checked (`StripArea.lean`): each triangle has signed doubled area `h^3*det(v,a)` and the signed total is `k*h^3*det(v,a)`. The value may be negative. Still open: absolute polygon-strip defect sums and their geometric decomposition, extension beyond rational times, varying force |
| 4 | Proposition I realization | Obligations P1–P5 are isolated in PROP_I_REALIZATION.md. Finite area/refinement identities, actual harmonic schedule bounds and matched-patch square covers are checked; see HARMONIC_REFINEMENT.md. Actual prefixes of one global dyadic family now construct Cauchy names and quotient values. Under T≥0 and T*(1+abs(w))≤1/2, BinaryTime and HarmonicTimeRealization derive time names, the proved time quotient, same-grid state control by 2*(1+abs(w))*M times actual time difference, and a continuous state map with endpoint/alias identities and zero cases. See CAUCHY_REALIZATION.md. PositionValues now derives planar values, gammaPosition, completed coordinate squares and positive sample position separation. Next: the same-time coarse polygon map and actual nonnegative between-path region/content. Independently rescaled rational-time identification, arbitrary partition independence and mechanical force identification remain separate. A supplied curve or scalar budget does not complete the primary target |
| 5 | Proposition II converse | Finite Case-1 step checked (Converse.lean): equal oriented areas ⇔ deflection cC parallel to SB; rational central kick when B≠S; counterexamples for unsigned areas, vertex at S, and the undetermined sense. Case 2 finite step (uniformly moving centre) and the unequal-cell converse (CentralSchedule.lean) also checked. Next: the vanishing-triangle passage with a justified realized curve, keeping direction and sense distinct |
| 6 | Proposition III relative motion | Finite integer-polygon step checked in `RelativeMotion.lean`: Corollary VI, Law I, relative deflection `d n − e n`, and relative-area converse. `propIII_via_moving_centre` explicitly cancels the reference history in both bodies, identifies the correctly timed uniform reference vertices, and applies Proposition II to the original relative-area hypothesis. No Law III, mass, force law or limit is derived. Open: the limiting passage from a realized relative orbit and any force/mass/time-scale interpretation |
| 7 | Proposition IV circular comparison | Closed **finite core** (`Comparison/CircleCompare.lean`): the exact intersecting-chords relation `s*(2r-s)=(c/2)^2` carried by a `CircleChord`, and equal-time `forceBySagitta` forces proportional to the sagittae (`force_ratio_is_sagitta_ratio`). The per-edition routes (1687 Prop II+Lemma V+Lemma XI; 1713 Prop II+Prop I Cor 2&4+Lemma VII) are the limiting steps that turn this into `arc^2/r`; they are documented as separate editorial interpretations, not derived, so the editions stay apart. Open: the limiting route itself and the force interpretation |
| 8 | Boundary/action diagnostic (arguments in `action-arguments/`; Arg004–Arg006 support action as the kind, location and scale of a constant, with no value fixed) | Open. Arg004 (Cavalieri strip, planar symplectic), Arg005 (rational-cell MonotoneEnclosure + identify `tri` with PartitionControl's cross statistic), Arg006 (discrete curvature radius vs `p^2/(m*|F_perp|)`) are specified but not yet formalized. Do not assume a universal constant |

For obligations 4–7, report a proved special case separately from the whole
proposition. If a historical premise cannot be recovered, continue independent
obligations while retaining that gap. A source-map entry is not a Lean theorem.

Order 4, current handoff: D.1 and the minimal foundation bootstrap are
recorded. Task A has a [sampling interface](GENERAL_FORCE_DESIGN.md),
constructed acceleration values, actual bounded polygon iterates and finite
mesh-uniform refinement accumulation. Continuous class (b) has local consistency
through its own modulus; full-family convergence and uniqueness are separate.
D.2 extracts the remaining generic completion/geometry/time layers into the
foundation. B.1 now closes reciprocal-dyadic E/G agreement and endpoint cases;
arbitrary numerators need an integer-refinement estimate. B.2 constructs
within-cell polygon names and a uniform whole-edge bound. Complete different-cell
alias independence and the quotient coarse map before the region/content
work in C.1. General motion realization, restart/gluing and derived confinement
remain obligations.
Task C.2's permitted parallel finite identities are in
[Arg007](action-arguments/261004gpt6.1solv1Arg007.md), without identifying D_mesh.

Validation is sequential and delegated. The final verification agent runs both
build targets and source/reference checks after implementation agents finish.
Use the formal-result ledger for actual theorem premises and the research state
for current completion boundaries. No task is marked complete solely because
a structure contains a field asserting its desired conclusion.
