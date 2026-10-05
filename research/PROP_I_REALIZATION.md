# Proposition I realization: premises and checked finite steps

TASKS.md order 4. This note identifies, stage by stage, what Proposition I
asserts, what its cited dependencies supply, and which further premises a
realization of the motion needs for a **varying** central force. Lean results
are modern rational-coordinate reconstructions (`modern_reconstruction`),
not historical proofs.

The [theorem-growth study](THEOREM_PROLIFERATION.md) separates implementation
inventory from discharged obligations. PolygonValues now shares the finite polygon alias/joining proof, and
GeneralForcePolygonCurve constructs the general whole-edge map;
the historical P1–P5 boundaries below stay unchanged.

The 4 October handoff's [foundation inventory](BARROWLIB_BOUNDARY.md) is
implemented for its minimal bootstrap. BarrowLib's generic finite triangular
maps now have actual iteration bounds, cross-map perturbation (including
sampling error E), local two-half/full-cell estimates and derived finite
mesh-uniform accumulation in the retained τ₀=1 gauge under T(1+L) ≤ 1/2. The comparison contract is global;
B and V bounds concern only the finite prefix used. [ForceClasses](GENERAL_FORCE_DESIGN.md)
constructs acceleration values, connects bounded iterates to actual Newton
schedules, and derives continuous-force local consistency from a modulus.
Harmonic and parallel fields remain instances. GeneralForceEndpoint now
constructs fixed-time endpoint Cauchy names/values from actual Lipschitz central
sample schedules, with derived geometric precision and adjacent error. Its
premises are global force comparison, a calibrated window, and bounded actual
coarse/first-half shadow samples; coarse velocity is derived. Harmonic force
bounds are derived on its short family, and the resulting general value equals
the old harmonic endpoint value. GeneralForcePrefix/GeneralForceTime now
construct a continuous local binary-time state/position map with uniform prefix
convergence, address independence, initial/zero values and full-endpoint E/G
agreement. The harmonic map is an exact corollary with all its bounds derived.
Local-annulus stability, confinement, restart/gluing, interior-time E/G and
precision/partition independence and unrestricted P5 remain
explicit obligations. D.2 extracts the generic completion, geometry,
binary-time and position-value layers. B.1 proves E/G agreement at every
dyadic rational time, with explicit finite numerator addresses and endpoint cases. B.2 constructs
within-cell polygon names and a mesh-explicit whole-edge bound. Both same-cell
and shared-boundary aliases agree before polygonMap is lifted to the time
quotient. Fixed-integer harmonic subdivision and its actual accumulated bound
now yield dyadic E/G agreement. TimeCalibration now proves the weighted gauge
|x|+τ₀|v|, actual finite sample-error accumulation, dimensionless growth/windows,
Cauchy-gauge equivalence and positive time-unit invariance. Harmonic and parallel
cells are instances; exact harmonic mechanics commute with unit rescaling.
C.1 now constructs the actual harmonic matched region as cell closures of
rational simultaneous connectors. Its nonnegative finite-square outer content
D_mesh has a derived 4*C²/2^m bound and decay. HarmonicPathContent constructs
its Cauchy scalar from the all-cover cut by shrinking intervals; lower-cut
identification and independence of the initial cover are proved. No scalar
area or Cauchy premise is supplied. GeneralForceSecants now derives uniform
convergence of completed bracketing dyadic position secants to constructed
velocity; HarmonicSecants applies it to the retained harmonic curve. These
are actual curve endpoints, including the final boundary, not finite polygon
secants alone. CompletedForce now constructs force values at completed
positions from the actual oracle samples, with representative independence,
Lipschitz control and precision-scale independence. Actual prefix force samples
converge uniformly to the force at the constructed curve; the retained harmonic
extension equals scaling by -w. GeneralForceAccelerationSecants now proves
uniform convergence of completed dyadic velocity secants to the force at the
constructed position, with derived bound H_m*L*(V+K) and a retained harmonic
corollary. Ordinary-area identification and unrestricted difference quotients
remain open.
GeneralForcePolygonCurve now constructs the actual quotient coarse polygon
with whole-edge error (T*V+A)/2^m and uniform convergence, including zero time
and shared initial endpoint. Six retained harmonic proofs now instantiate the
shared PolygonValues core with unchanged theorem statements; the general
harmonic polygon equals the retained map. GeneralForcePathRegion/Content now
construct the actual general closed-cell connector union and its all-cover cut
and canonical scalar, with budget 4*C²/2^m, nonnegativity, zero time and decay.
MatchedRegion shares closure/connector/cover geometry with the retained harmonic
client. Their harmonic instance has exactly the old region and scalar content,
independently of the different initial cover bounds.
QuadraticEstimates now derives the actual finite second-order position
remainder t²*(L*t*V+E) and exact t*h*|a(x0)|/2 half-mesh bias. The actual
parallel endpoint family constructs Cauchy values at every nonnegative rational
time and proves the exact quadratic state. Galilean potential and triangle
identities apply to those completed endpoints with the half coefficients; the
ratio stays motion-dependent. GeneralForceQuadraticSecants now passes the
actual finite remainders to completed central curve values. The normalized
position departure 2*(Delta_x/H-v_left)/H converges uniformly to the completed
force with error H*L*(2V+K), including the final boundary. Cauchy-name tail
boundedness proves that mesh times the actual force sample magnitude vanishes;
no extra force-bound or Taylor field is supplied. The retained harmonic curve
inherits the result. Curved potential steps, unrestricted second-order
quotients and the D_mesh relation remain open. Completion scores stay unchanged.
The foundation has no import from a Newton-specific file and no derivative,
integral or ODE primitive.

The governing target is the **unsupplied-curve construction variant**. The main
area BETWEEN polygon and actual trajectory is distinct from the Kepler area
swept by the radius. See [path defect](PROP_I_PATH_DEFECT.md) for all three
stage interfaces and separate existence/enclosure obligations. Estimates
against a supplied curve are conditional diagnostics only.

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
with no numbered limiting lemma (M2.md).

## Obligations and status

| Obligation | Status |
| --- | --- |
| P1 finite area law | **Checked in the rational planar model, generalized**: `CentralSchedule.swept_eq` holds for any central field and arbitrary *unequal* rational cells. Newton uses equal cells. |
| P2 refinement family | **Exact finite identities**: for any field, splitting a cell `h+k` moves the endpoint by exactly `h*k*a(y)` (`refine_position`). The velocity changes by `h*(a y − a X) + k*(a z − a X)` (`refine_velocity`). The harmonic example proves both changes are nonzero while swept areas agree. The refined polygons are different polygons. |
| P3 existence of the ultimate curve | **Open for the general historical claim.** Lemma III Cor. 4 (1687 par10, 1713 par11) concerns rectilinear figures built on a given curve; it does not construct this moving-vertex family. Constant-force candidate/residual bounds and harmonic finite stability/refinement bounds are checked. For the harmonic field under T≥0 and T*(1+abs(w))≤1/2, actual prefixes of one global dyadic family now construct Cauchy names, quotient state values and a continuous map on the constructed binary-time quotient. BinaryTime derives the time names; HarmonicTimeRealization proves same-grid control by 2*(1+abs(w))*M times actual time difference, address independence, endpoint/alias identities and zero cases. No curve or limit point is supplied. See CAUCHY_REALIZATION.md and HARMONIC_REFINEMENT.md for the estimates and premises. PositionValues now derives the planar gammaPosition map, coordinate squares and positive sample position separation. Identification with independently rescaled values is proved at every dyadic rational time. GeneralForceTime now gives the local binary-time map for globally compared Lipschitz central samples with explicit actual/coarse/shadow bounds and calibration, with uniform prefix convergence and full-endpoint agreement; the old harmonic map is an exact corollary. Local-annulus stability, gluing, other general E/G time parameters, precision/partition independence, external real-time identification and merely continuous-force existence/uniqueness remain separate. |
| P4 intervening defect and area law | **Outer-content candidate checked for harmonic and general Lipschitz constructed curves.** GeneralForcePathRegion/Content use shared MatchedRegion cell/connector/closure geometry and actual vertex/prefix enclosures. Their harmonic specialization equals the old region and scalar content exactly. HarmonicPathRegion defines the cell closures of rational connectors between simultaneous polygonMap/gammaPosition values and their finite union. Initial endpoints agree and the final connector is included. Crossings and overlaps count once in the set; square budgets count multiplicity. D_mesh is the closed lower cut of the infimum of all finite square-cover budgets, with nonnegativity, a derived 4*C²/2^m bound, zero time and decay proved. HarmonicPathContent now realizes this cut as a cover-independent Cauchy scalar with the same bound, nonnegativity, zero time and decay. Ordinary-area identification and transfer of the separate Kepler law K_mesh remain open. HarmonicCover's polygon/refinement budget remains a distinct finite object. |
| P5 force identification | **Partial constructed rate bridge checked.** GeneralForceSecants proves that completed bracketing dyadic position secants converge uniformly to the constructed velocity under the stated global Lipschitz comparison, calibrated window and actual/coarse/shadow sample bounds. Finite O(t²) drift remainders are derived from restarted runs and pass to the completed curve; the harmonic result is a corollary. CompletedForce constructs the force at completed positions; GeneralForceAccelerationSecants now proves uniform convergence of completed bracketing dyadic velocity secants to this force with bound H_m*L*(V+K), including the final boundary. Finite force variation, rounding-error exhaustion and precision-offset invariance are derived; the retained harmonic acceleration-secant result is a corollary. Unrestricted difference-quotient differentiation remains open. "Aget indesinenter" is not imported as a modern proof premise. |

## Candidate permitted premise for P3

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

The harmonic field now has derived mesh-uniform actual state and endpoint-error
bounds, a proved square enclosure and nonnegative cover budget for matched
polygonal patches, and constructed fixed-rational-time endpoint Cauchy names;
see [harmonic refinement](HARMONIC_REFINEMENT.md). Uniform variation with
rational time is now derived in HarmonicTimeComparison, with an explicit
positive tolerance controlling every approximant. HarmonicBinaryPrefix now
constructs Cauchy names from actual intermediate-time prefixes of one global
polygon family. CauchyValues now realizes them in an explicit quotient and
proves representative-invariant time/tail bounds. BinaryTime and
HarmonicTimeRealization now construct the time quotient and continuous state
map, including endpoint/alias identities. PositionValues now derives the planar
position map, completed coordinate squares and positive position separation.
Addresswise same-time coarse polygon names and uniform whole-edge distance
control are now proved in HarmonicPolygonCurve. Both kinds of alias independence
construct polygonMap on the same time quotient. HarmonicPathRegion now
constructs the closed matched region, its all-cover infimum lower cut and a
derived vanishing square enclosure. See TRAJECTORY_DEFECT_REGION.md.
Cauchy scalar realization and cover independence are now proved in
HarmonicPathContent. Ordinary-area and Kepler-area identification, P5 and partition
independence remain distinct. CompletedForce now proves representative compatibility for globally Lipschitz
sampled force data; finite centrality alone does not supply it.
The [construction ledger](CAUCHY_REALIZATION.md) records the checked quotient
and time-domain steps and the remaining geometric obligations.

For a general varying field, any force-difference premise must be explicit and
named: a Lipschitz-type bound is a modern repair; the 1713 monotone-finite
qualification on a radial segment is an editorial candidate and does not alone
control a force vector's change of direction. No ODE theorem is imported.
