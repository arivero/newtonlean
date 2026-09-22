# Book I, Section II: three proof architectures

This is the source and premise map for the approved target in
[GOALS.md](GOALS.md). It does not certify the existing conditional Lean
reconstructions as Newton's proofs. *De Motu* has no retrospective Proposition
I--IV numbering here: only statements actually found in the inspected passages
are aligned.

## De Motu witnesses

The witnesses remain separate because NATP00089 retains additions and deletions
whose relative chronology is unresolved.

| Target | NATP00089 | NATP00090 | Finding |
|---|---|---|---|
| Area law antecedent | [par8--9](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par8): `areas temporibus proportionales`; finite impulses followed by `triangula numero infinita et infinitè parva` | [par16--17](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par16): same theorem; the proof explicitly marks Law 1 and Lemma 1 | Clear antecedent of printed Proposition I. The finite equal-area construction is identifiable; uninterrupted force and a realized limiting curve are asserted rather than separately constructed. |
| Converse area law | no counterpart found in inspected par1--19 | no counterpart found in inspected par1--28 | Bounded absence only; no Proposition II analogue is supplied by later texts. |
| Relative moving-centre result | no counterpart found in inspected par1--19 | no counterpart found in inspected par1--28 | Bounded absence only; no Proposition III analogue is supplied by later texts. |
| Circular-force comparison | [par10--11](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par10): `arcuum simul descriptorum quadrata applicata ad radios`; tangent departures are diminished indefinitely | [par18--19](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par18): same statement and route | Antecedent of printed Proposition IV. Neither proof cites a numbered limiting lemma. The force/departure identification and radius substitution remain obligations. |

NATP00089 par9 contains changing marginal labels (`Hyp. 1`, deleted `Hyp. 3`,
added `Lem. 1`). Because the revision order is not established, those labels are
not converted into accepted graph edges. NATP00090 par17 cleanly cites Law 1
and Lemma 1, and those same-stage dependencies are recorded.

## 1687

The section begins at [NATP00077 par43](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par43).

| Proposition | Statement and proof | Explicit dependencies | Formalization boundary |
|---|---|---|---|
| I | [par44--45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par44), `Areas ... esse temporibus proportionales`; increase triangle number and decrease width without bound | Law I; corollary 1 of the laws; Lemma III corollary 4 | Finite equal areas are reconstructed. Still required: compatible joining of cells, a refinement relation, a time-to-position map, convergence to the asserted curve, and identification of the limit with uninterrupted central action. |
| II | [par48--50](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par48), `areas ... temporibus proportionales ... vi centripeta`; the direction is inferred at vanishing triangles | Law I; Law II; Euclid I.40; corollary 5 of the laws for the uniformly translating case | Requires a realized plane curve and local deflection direction. Equality of small triangle areas alone must be connected to the force-producing change of motion. |
| III | [par53--54](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par53), force on the first body is composed from a central remainder and the second body's acceleration | Corollary 6 of the laws; Law I; Proposition II | Requires a common-time relative-motion construction and justified subtraction/composition of accelerative forces. Corollary VI states invariance under equal parallel accelerations; it does not construct the underlying trajectories. |
| IV | [par60--61](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par60), `arcuum simul descriptorum quadrata applicata ad ... radios` | Proposition II; Lemma V; Lemma XI | Requires nondegenerate circles and radii, uniform motion, tangent-departure/force identification, and the ultimate-ratio substitutions. Lemma XI carries its finite nonzero curvature restriction from par39. |

The mechanical premises are [Law I](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par1),
[Law II](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par3),
[corollary V](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par20), and
[corollary VI](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par22).
The imported Euclidean result is cited by Newton at par49; the graph records it
as an imported-geometry node rather than pretending to derive it from Lean core.

## 1713

The section begins at [NATP00082 par49](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par49).

| Proposition | Statement and proof | Explicit dependencies | Material change or retained boundary |
|---|---|---|---|
| I | [par50--51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par50), again `Areas ... esse temporibus proportionales` | Law I; corollary 1 of the laws; Lemma III corollary 4 | The finite-to-continuous assertion remains. Corollaries 2 and 4 now become explicit inputs to Proposition IV. |
| II | [par58--60](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par58) | Law I; Law II; Euclid I.40; corollary 5 of the laws | Same local direction and realized-curve obligations as 1687. The statement explicitly says the curve is described in a plane. |
| III | [par64--65](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par64) | Corollary VI of the laws; Law I; Proposition II | Same relative-motion and force-composition obligations, with bodies L and T named in the proof. |
| IV | [par71--72](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par71) | Proposition II; Proposition I corollaries 2 and 4; Lemma VII | This is a different explicit proof route from 1687: centre direction and equal-time sagittae come through Proposition I's corollaries, and Lemma VII supplies the arc/chord/tangent ultimate ratio. Circle nondegeneracy and force identification remain explicit formal obligations. |

The edition-local laws are [NATP00081 Law I](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par1),
[Law II](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par3),
[corollary V](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par20), and
[corollary VI](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par22).

## Shared proof obligations and diagnostic separation

The historical theorem interfaces must expose these obligations rather than
contain their conclusions as structure fields:

1. **Finite motion:** equal time cells, inertial continuations, central impulse
   directions, and Euclidean area equalities.
2. **Gluing:** adjacent cells share position; their incoming/outgoing motion
   data either match or have a specified impulse jump. Boundary cancellation is
   a finite identity, not an invocation of Gauss's theorem.
3. **Refinement:** state which old times, positions and impulse data survive.
   An arbitrary finer polygon is not automatically compatible with the coarser
   one.
4. **Trajectory realization:** construct a map from times to points and prove
   the needed convergence and partition independence. Scalar swept-area
   convergence does not give this map.
5. **Force identification:** connect the limiting change of motion to the
   edition's definition and Law II, separately from geometric convergence.

The current finite `Polygon` and `Contact` results may be cited as modern
diagnostics for these obligations. They do not supply a historical edge unless
Newton's same-stage text supplies it. Any action-valued boundary residual or
fixed-constant proposal belongs to the separate diagnostic layer in
[GOALS.md](GOALS.md); it cannot close an edge in these proof maps.

## Finite Proposition II step (22 September 2026)

`Polygon/Converse.lean` reconstructs Case 1's finite step in integer
coordinates with S at the origin (1687 par49, 1713 par59). With `c` the
inertial continuation of AB and C the next vertex, `equal_area_parallel` and
`parallel_equal_area` prove that equal **oriented** triangles SAB, SBC are
equivalent to `cC` parallel to SB. `equal_area_central_step` then gives a
rational central kick when B ≠ S, and `equal_areas_all_central` applies it to
every cell of an equal-area vertex sequence. Three checked examples keep the
remaining premises visible. Equal unsigned areas with opposite orientation
admit a non-central deflection, which matches Euclid's "same side" condition.
A vertex at S fixes no direction. Outward and inward kicks give equal areas
alike, so "tendentes ad punctum S" (toward rather than away) needs a further
premise. Both editions cite Euclid I.40. In Heath's numbering I.39 is the
same-base statement and I.40 concerns equal bases, while Newton's triangles
SBc, SBC share the base SB. The citation is recorded as printed, and the
numbering of the Euclid edition Newton used was not investigated
(`editorial_interpretation`, low confidence). For Case 2 (par50, par60),
`extend_relative` proves that inertial continuation commutes with uniform
translation of the centre, and `moving_centre_equal_areas_central` transfers the
finite step to a uniformly moving centre. This is a finite coordinate
counterpart of the use of Corollary V, which itself concerns motions within a
uniformly moving space. Unequal cells and the vanishing-triangle passage from
a realized curve remain open.

## Confidence and stopping point

All accepted proof edges added for this map are explicit same-stage citations
and have high confidence. The De Motu absence claims are deliberately limited
to the inspected local witnesses and ranges. No claim is made here about an
uninspected manuscript counterpart, trajectory existence, continuous-force
existence, or a mathematical obstruction to classical repair.
