# Polygon–trajectory area: Theorem 1 / Proposition I

Current status and open obligations are maintained in [STATE.md](STATE.md).
Follow [the current handoff](HANDOFF-2026-10-06-REWORKED-SOURCES.md);
this note retains the source argument and mathematical scope.

## The two areas

For a constructed polygon P_mesh and the eventual trajectory gamma over the
same time interval, D_mesh is the **nonnegative area of the intervening region**.
Shared endpoints must be proved or endpoint connectors explicitly supplied.
Crossing paths require nonnegative accounting for each lobe, with a justified
geometric decomposition and overlap/multiplicity convention.

K_mesh is the separate Kepler area swept by a radius from the force centre.
The finite equal-cell law controls K_mesh. It constructs neither gamma nor
D_mesh. A signed sector-area difference can express a closed-boundary identity,
but its absolute value can erase opposite lobes. It is not a definition of D_mesh.

The checked finite example in `Polygon/PathDefect.lean` compares
(0,3)→(1,3)→(2,3) with (0,3)→(1,4)→(1,3)→(1,2)→(2,3).
Both have signed doubled Kepler sum -6 and unsigned doubled Kepler sum 6 about
S=(0,0). Their intervening triangle lobes have signed contributions -1 and +1,
but doubled unsigned areas 1 each. The absolute patch budget is 2. The triangle
interiors occupy adjacent ranges 0<x<1 and 1<x<2; the Lean result verifies
finite determinant arithmetic, not a general theory of planar regions or a
mechanical trajectory.

## Separate stage-local approximation obligations

| Stage | Passage and witness | Supported premise and remaining construction |
| --- | --- | --- |
| De Motu NATP00089 | [Theorema 1, par8–9](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par8) | Explicit polygon followed by infinitely small triangles. High confidence. Marginal revision chronology remains unresolved; no printed limiting lemma is imported. Take gamma as given under the user-authorized convention; prove the swept-area law and control D_mesh using this witness's permitted data. |
| De Motu NATP00090 | [Theorema 1, par16–17](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par16) | Explicit polygon, Law 1/Lemma 1 references, and final limiting assertion. High confidence. Keep this witness distinct; prove the area law and D_mesh control for given gamma without borrowing NATP00089's unresolved labels. |
| 1687 | [Proposition I, par44–45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par44) | `explicit_dependency`, high confidence: this edition's Law I, laws' Corollary 1 and Lemma III Corollary 4. Take the trajectory as given; identify the moving-vertex impulse approximation with it and justify D_mesh control. The area law remains the conclusion. |
| 1713 | [Proposition I, par50–51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par50) | The same explicit citations in this edition, high confidence. Separately scoped given trajectory, D_mesh control and force identification; no silent 1687 or later premise. |

The D_mesh obligation is a `modern_reconstruction` of the user's question,
not a separate defect-area theorem quoted from Newton. Exact passages were
read from the local TEI-backed store; normalized NATP00089/90 were also checked
online. No manuscript-image or revision-chronology resolution is claimed.

## Checked support and open main proof

Separate stage modules give finite unsigned equal-cell/block statements.
These remain supporting K_mesh results under explicit Euclidean identities
and supplied area semantics. They count triangles with multiplicity.

`PathDefect.signed_gap_eq_Kepler_difference` proves a finite boundary identity;
`signed_gap_abs_le_budget` and `absolute_budget_le_count_mul` prove nonnegative
local-to-global control; translation preserves the patch budget. The inputs
are two finite polygons with matched spatial patch endpoints. They do not yet
constitute a force/time-compatible refining family or an actual trajectory.

The stage-local `polygon_trajectory_defect_control` theorems are explicitly
**conditional area-control interfaces**. Their scalar region function must
have the stated geometric meaning, and their enclosure and vanishing budget
still require proofs. Given-curve results are now permitted in the primary
route, but an assumed scalar enclosure does not complete the approximation
proof or establish Proposition I's swept-area conclusion.

The harmonic field now has actual common-time refinement, uniform state/error
bounds and a finite geometric cover in `HarmonicCover.lean`. Both matched
half-cell point regions fit a square of radius h*M*(4+3*T*|w|) about the coarse
start. The summed square budget 2*T*h*M²*(4+3*T*|w|)² is nonnegative and
counts multiplicity; it is neither Kepler area nor actual union/trajectory
area. No curve is an input to this construction.

HarmonicDyadic now constructs endpoint Cauchy names at fixed rational times,
with a derived tolerance modulus and no supplied limit point.
HarmonicTimeComparison now controls their variation with rational time,
uniformly in the refinement level, and constructs an explicit positive
continuity tolerance. HarmonicBinaryPrefix now constructs intermediate-time
Cauchy names from actual prefixes of one global polygon family, for every
binary address, with a derived geometric tail. CauchyValues now constructs
their quotient state values and transfers the actual time/tail bounds after
proving representative invariance. BinaryTime and HarmonicTimeRealization now
derive the time names, their proved quotient and a continuous state-value map
on it. Equivalent addresses, endpoints and zero cases are checked. PositionValues
now derives planar values, the continuous position map and coordinate-square
predicates, including a positive position separation proof. HarmonicPolygonCurve
constructs the same-time quotient polygon map. HarmonicPathRegion constructs
cell closures of rational connectors to gammaPosition and their finite union.
Initial endpoints agree; the explicit final connector remains even when finite
endpoints differ. Reversing a connector leaves its region point unchanged.
D_mesh is the closed lower cut of the infimum of all finite square-cover
budgets, with nonnegativity, the derived 4*C²/2^m bound, zero-time content and
positive-tolerance decay proved. This is a modern matched-region outer-content
candidate, not a signed boundary area or an identified Euclidean measure.
HarmonicPathContent realizes this cut as a scalar with the same bound and decay,
using derived bisection Cauchy data and proving cover independence.
Arbitrary partition independence,
ordinary sector-union area identification and edition-local uninterrupted-force
identification remain separate. No integral calculus, ODE theorem, measure
theorem, or silently supplied completion closes these obligations.
