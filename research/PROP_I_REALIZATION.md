# Proposition I realization: premises and checked finite steps

TASKS.md order 4. This note identifies, stage by stage, what Proposition I
asserts, what its cited dependencies supply, and which further premises a
realization of the motion needs for a **varying** central force. Lean results
are modern rational-coordinate reconstructions (`modern_reconstruction`),
not historical proofs.

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
| P3 existence of the ultimate curve | **Open.** Lemma III Cor. 4 (1687 par10, 1713 par11) concerns limits of rectilinear figures built on a given curve; it does not construct this moving-vertex family. Constant-force candidate and residual/mesh bounds are checked at rational times. For the harmonic field, the discrete invariant and its speed/position bounds have explicit coefficient and margin premises in HarmonicStability. HarmonicAccumulation compares actual equal-time schedules, and HarmonicUniform derives state bounds ≤2M and actual error ≤3*T*h*abs(w)*M under h≥0 and its named small-time condition. HarmonicCover encloses matched rational points inside cells; HarmonicDyadic constructs actual endpoint Cauchy names at fixed rational times, with finite-gap bound 3*T²*abs(w)*M/2^j and an explicit positive-tolerance modulus. HarmonicTimeComparison constructs their rational-time map and derives uniform levelwise time control, with positive delta=eps/(L+1). HarmonicBinaryPrefix constructs actual intermediate-time prefix Cauchy names for every binary address of one global dyadic family, with derived finite-gap/two-sided tails and an explicit modulus. CauchyValues constructs quotient state values and proves representative-invariant time/tail bounds; it supplies no external limit point or curve. Identification of equivalent time descriptions and a continuous map on the constructed time quotient, partition independence and general varying-force convergence remain open. |
| P4 intervening defect and area law | **Open for the actual trajectory.** HarmonicCover derives a finite coordinate-square cover for both matched half-cell patches of each actual coarse/fine block. Its nonnegative, multiplicity-counted budget is 2*T*h*M²*(4+3*T*abs(w))². It proves point-set containment, not union content or D_mesh for an unconstructed trajectory. Construct that region and derive its vanishing enclosure without cancellation of opposite lobes. `swept_eq` controls the distinct Kepler area K_mesh; transferring its law to the constructed curve requires geometric identification. |
| P5 force identification | **Open.** "Aget indesinenter" identifies the impulse limit with a continuous force; no finite result supplies this. |

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
proves representative-invariant time/tail bounds. Next identify equivalent
time descriptions and construct a continuous map on their quotient before
asserting a trajectory on that time domain.
Completion/realization, transfer of the
cover to a trajectory, content/area identification and partition independence
remain distinct. A general represented-point force also needs compatibility
with point value equivalence; finite centrality alone does not supply it.
The [construction specification](CAUCHY_REALIZATION.md) records the quotient,
time-domain and geometric obligations before those constructions are attempted.

For a general varying field, any force-difference premise must be explicit and
named: a Lipschitz-type bound is a modern repair; the 1713 monotone-finite
qualification on a radial segment is an editorial candidate and does not alone
control a force vector's change of direction. No ODE theorem is imported.
