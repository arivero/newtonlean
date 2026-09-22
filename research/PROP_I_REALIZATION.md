# Proposition I realization: premises and checked finite steps

TASKS.md order 4. This note identifies, stage by stage, what Proposition I
asserts, what its cited dependencies supply, and which further premises a
realization of the motion needs for a **varying** central force. Lean results
are modern rational-coordinate reconstructions (`modern_reconstruction`),
not historical proofs.

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
| P1 finite area law | **Checked, generalized**: `CentralSchedule.swept_eq` holds for any central field and arbitrary *unequal* rational cells. Newton uses equal cells. |
| P2 refinement family | **Exact finite identities**: for any field, splitting a cell `h+k` moves the endpoint by exactly `h*k*a(y)` (`refine_position`). The velocity changes by `h*(a y − a X) + k*(a z − a X)` (`refine_velocity`). The harmonic example proves both changes are nonzero while swept areas agree. The refined polygons are different polygons. |
| P3 existence of the ultimate curve | **Open.** Lemma III Cor. 4 (1687 par10, 1713 par11) says the ultimate figures of Lemmas II–III, built on a *given* curve `acE`, are *rectilinearum limites curvilinei*. It states no convergence of the Prop I polygon family, whose vertices move under refinement (P2). For constant force the convergence is checked at rational times (PARTITION_CONTROL.md). For varying force, P2 shows that the missing premise is control of force differences at the scale of the cell displacements. **Stability, one varying field checked**: for `a(p) = -w*p` (Prop. IV Cor. 3 case), `HarmonicStability.schedule_invariant` conserves `w\|x\|² + w*d*(x·v) + \|v\|²` exactly over equal cells, and `invariant_square` completes it to `w\|x + (d/2)v\|² + (1 − w*d²/4)\|v\|²`, so orbits stay bounded when `w*d² < 4`. Convergence is still open. |
| P4 area law in the limit | **Conditional on P3.** `swept_eq` is exact at every mesh, so the limit area would be `t*L`. The area of the limit curve still needs an enclosure notion (M2 `sector_ratio_reconstruction`). |
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

The harmonic field already has a mesh-uniform bound. Combining it with the
exact refinement identities of P2 is the natural first convergence test.

State P3 for a varying field as a discrete stability estimate at rational
times. The premise should be explicit and named: either a Lipschitz-type bound
on force differences (modern), or the 1713 monotone-finite qualification on a
radial segment (editorial). Prove it by finite induction, with no ODE theorem.
