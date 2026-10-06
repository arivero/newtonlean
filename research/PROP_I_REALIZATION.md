# Proposition I realization: premises and checked finite steps

Current status and open obligations are maintained in [STATE.md](STATE.md).
Follow [the current handoff](HANDOFF-2026-10-06-REWORKED-SOURCES.md);
this note retains the source argument and mathematical scope.

## What the text asserts

1687 [NATP00077 par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45)
and 1713 [NATP00082 par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51)
share the argument almost verbatim:

1. *Dividatur tempus in partes æquales*: equal time cells.
2. Law I gives the inertial continuation `Bc = AB`; Corollary 1 of the laws
   places the body at C after a single impulse at B toward S.
3. Parallels `SB ∥ cC` give equal triangles, and *componendo* the sums of
   areas are as the times.
4. *Augeatur jam numerus & minuatur latitudo triangulorum in infinitum*:
   by Lemma III Cor. 4 the ultimate perimeter is a curve, the force acts
   *indesinenter*, and the areas remain proportional to the times.

De Motu Theorem 1 (NATP00089 par9, NATP00090 par17) makes the same passage
with no numbered limiting lemma (see the historical AreaLaw file).

## Proof dependencies and the implementation route

The following chain was checked against the **proof paragraphs** of the
archived TEI on 5 October evening, rather than inferred from the order of the
statements. The historical Lean comments and this source route record the witness,
passage, URL, classification and confidence. The finite composition proofs
retain their source correspondence. The remaining limiting edges are still obligations; a reference
records a reconstruction, not certification of the full historical step.

| Proof step | 1687 proof passage | 1713 proof passage | Dependency and formal obligation |
| --- | --- | --- | --- |
| Rectilinear continuation and impulse composition | [Prop. I par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45) | [Prop. I par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51) | Law I and the laws' Corollary 1 are explicit citations. The finite drift/kick construction must reproduce the inertial continuation and the radial deflection before proving equal triangles. `CentralSchedule.cell_momentum`, `det_cell_area` and `swept_eq` supply the rational planar reconstruction. |
| Why the parallelogram gives the position | [Laws Cor. 1 proof par8](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par8) | [Laws Cor. 1 proof par8](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par8) | Both proofs use unchanged transverse approach velocity and the intersection of two parallel lines. `uniform_endpoint_lines` now derives those constraints in the rational mechanical model, then `intersection_unique` derives the opposite corner. `next_arrival_diagonal` connects composition to the actual central cell. Only 1713 explicitly cites Laws II/I and initial impulses; the separate 1687 model specialization does not attribute those clauses to its text. |
| Finite composition of the areas | [Prop. I par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45) | [Prop. I par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51) | The equal-triangle argument is iterated and the areas are added. The separate edition `finite_componendo` results and `CentralSchedule.swept_eq` implement this finite step. Constant areal product alone does not implement the swept-area conclusion. |
| Curvilinear perimeter | [Lemma III Cor. 4 par10](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10) | [Lemma III Cor. 4 par11](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11) | Proposition I explicitly cites this corollary. *Et propterea* refers to the preceding rectangle/chord/tangent figures, now traced in separate source edges. The given-curve chord case has a proved two-sided closed-boundary limit with an explicit uniform modulus. The actual general force curve derives its own modulus, and its varying polygons have their own proved whole-edge boundary limit. Finite rational monotone supporting cells now have derived crossings, rectangle enclosures and two-sided whole closed boundary limits. Tangent identification and the full historical curvilinear-area enclosure inference remain open; no arclength claim is made. |
| Unequal widths reduce to the largest width | [Lemma III proof par6](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par6) | [Lemma III proof par7](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par7) | Lemma III reuses Lemma II's figures and equal limiting ratios implicitly (*Eædem rationes ultimæ*), then bounds the gap by the rectangle of maximum width. `rectangle_gap_bound` retains the integer arithmetic. The fixed-interval monotone graph reconstruction now derives completed lower/upper point-set enclosure, constructs the actual largest width and proves the rational rectangle-sum gap bound and exhaustion. Identification with ordinary geometric union area and the actual motion remains separate. |
| The enclosing rectangle becomes arbitrarily small | [Lemma II proof par4](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par4) | [Lemma II proof par5](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par5) | Lemma II identifies the gap with one width times total height and explicitly invokes Lemma I. The rational graph reconstruction now proves the exact equal-width rectangle-sum gap and its exhaustion. The actual path-content budget and grounded `polygon_trajectory_enclosure` remain separate modern square-content results. Ordinary union-area and the ultimate curvilinear-area ratio remain open. |
| Approach closer than any assigned difference gives equality | [Lemma I proof par2](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par2) | [Lemma I proof par3](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par3) | Newton assumes a final difference D and contradicts the approach hypothesis. The current rational exhaustion and quotient equality arguments justify their particular constructed limits. A general historical ultimate-ratio certificate is a separate obligation. |

De Motu keeps its own chain. [NATP00090 par17](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17)
cites its Law 1 and Lemma 1; the [Lemma 1 proof par11](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par11)
contains the marked addition *per Legem 2*. [NATP00089 par9](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par9)
has changing marginal hypothesis/lemma labels whose chronology is unresolved.
Both proofs pass to infinitely many infinitely small triangles without citing
a numbered limiting lemma. Neither witness inherits the printed Lemma III.

The primary proof route takes the trajectory as given: justify Newton's finite
construction and equal triangles, derive the approximation and intervening
control from independently stated motion premises, and connect the finite
areas to ordinary swept-sector area through the invoked historical lemmas.
`GeneralForceArea.constructed_area_law` supplies a modern supporting fan law
for the existing local regional Lipschitz construction. Its
regularity/window premises are a **modern reconstruction**, not assumptions
read into Newton's proof. Ordinary sector-union area, unrestricted force/rate
identification and the historical limiting passage remain explicitly separate.

## Obligations and status

| Obligation | Status |
| --- | --- |
| P1 finite area law | **Checked in the rational planar model, generalized**: `CentralSchedule.swept_eq` holds for any central field and arbitrary *unequal* rational cells. Newton uses equal cells. |
| P2 refinement family | **Exact finite identities**: for any field, splitting a cell `h+k` moves the endpoint by exactly `h*k*a(y)` (`refine_position`). The velocity changes by `h*(a y − a X) + k*(a z − a X)` (`refine_velocity`). The harmonic example proves both changes are nonzero while swept areas agree. The refined polygons are different polygons. |
| P3 trajectory existence and identification | **Existence postulated in the primary route, 6 October; identification remains to prove.** Supply a trajectory map, its separately stated mechanical laws and any required regularity. Do not assume that Newton's polygons converge to it or that either area conclusion holds. The verified `GeneralForceEndpoint`/`Prefix`/`Time` construction remains supporting work, including its regional assumptions and open gluing/partition questions. |
| P4(A) swept-area law, the Proposition I conclusion | **Constructed-curve and conditional given-motion fan laws checked; historical given-trajectory proof open.** `SweptArea.Proportional` states the all-interval fan-area target, with the curve provided as data. `GeneralForceArea.proportional_swept_area` derives the retained regional instance from the checked interval law. The actual curve-node fans give `abs(ell)*abs(t1-t0)/2`; existence of the fan limit is part of the conclusion. Unsigned fans count multiplicity. Ordinary sector-union identification and the historical limiting passage remain open. No area law is assumed in the trajectory postulate. |
| P4(B) between-path approximation control | **Retained constructed-curve content control checked; bridge to an independently given mechanical trajectory open.** `GeneralForcePathContent.polygon_trajectory_enclosure` and `polygon_trajectory_defect_vanishes` ground actual matched-region all-cover content with bound `4*C²/2^m`. Initial endpoints agree and the final connector is retained. This set counts overlaps once and is distinct from swept fan area. Its convergence is not part of trajectory existence, and equal swept sums alone do not prove it. |
| P5 force identification | **Constructed dyadic rate bridges checked.** `GeneralForceSecants` identifies completed bracketing position secants with constructed velocity; `GeneralForceAccelerationSecants` identifies completed bracketing velocity secants with force at the constructed position, uniformly including the final boundary. `CompletedForce` operates on the certified regional completion domain and is independent of force precision. Restarted finite remainders and exhaustion derive the estimates; harmonic results are corollaries. Unrestricted difference quotients, motion-precision/partition independence and historical justification of continuously acting force remain open. |

## Regularity questions retained separately from existence

Proposition I cites no premise on the force's regularity. The nearest
same-stage qualification is in Lemma X, which Proposition I does not cite:

- 1687 [par27](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par27):
  *urgente quacunque vi regulari*.
- 1713 [par28](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par28):
  *urgente quacunque Vi finita … sive Vis illa determinata & immutabilis sit,
  sive eadem continuo augetur vel continuo diminuatur*.

Importing this qualification into Proposition I would be an
`editorial_interpretation` and needs its own justification. The 1713 form is
the more usable one. A finite force that is monotone along a path segment has
bounded variation there, so the velocity change in P2 telescopes like the
Lemma III width argument already checked in `rectangle_gap_bound` (M2). The
force is a vector, however. Monotone magnitude leaves the change of
direction to control, which needs the radius bounded away from S
(compare the vertex-at-S counterexample in `Converse.lean`).

Any such regularity premise brings a scale. A Lipschitz bound `L` on the
force defines a local dynamical time `1/√L`; the finite consistency estimates
require the cell small compared with the relevant local scales. Newton's clauses assert finiteness
without a value: they fix the existence of a scale, and its size depends on
the law and the region. The retained harmonic bounds use τ₀=1. The new
calibrated finite estimates use `|x|+τ₀|v|` and the dimensionless window
`n|h|(1/τ₀+τ₀L) ≤ 1/2`, with proved positive time-unit invariance; see [scales and units](GENERAL_FORCE_DESIGN.md#scales-and-units).

## Converse side

`CentralSchedule.unequal_cells_converse` extends the finite Proposition II step
to unequal cells. If two consecutive doubled areas are proportional to their
nonzero durations, the impulse at the shared vertex is parallel to its radius.
Proposition II's statement speaks of areas proportional to times, so this is
the finite content it needs when cells are unequal.

## Next bounded step

Follow the current handoff: formalize the two missing historical Lemma I
proofs, then identify the rectangle side-product sums with geometric union
area and apply that lemma to the actual enclosed curvilinear quantity.
Preserve nonzero area where a ratio requires it. The source-local corollary
chain and Proposition I's swept-sector conclusion follow those invoked steps.
Modern given-motion consistency remains additional supporting proof work;
it is not a reason to reconstruct trajectory existence or to import a modern
limit theorem as the primary historical argument. Tangent identification,
vertical patches, ordinary sector area and unrestricted force remain open.
