# Review of docs/reference/principia-with-lean.md, 5 October 2026

Reviewer: a Claude Fable 5.1 subagent, reading only the interleaved document (the full Lean source as printed at commit cb0d4c4) with no other file open. Requested by the user; relayed unedited. Line numbers refer to the document at that commit. The document-side items (14–24) were corrected in the generator afterwards; the Lean-side items (1–12) are recorded as tasks in HANDOFF-2026-10-04-GENERAL-FORCE.md.


Scope: this one file only, read sequentially in full (25,588 lines in the
current version; the file was regenerated at 19:09:07 while the review was in
progress, and all line numbers below refer to the current version). After the
sequential read, text-only cross-checks were run over the printed Lean:
every `structure` declaration and its instantiation, every `Prop`-valued
predicate and whether it is ever proved unconditionally, one-line alias and
projection proofs, forbidden keywords, Verbatim balance, module headers versus
`import` statements, and the stated theorem and line counts.

Global result: no `sorry`, `axiom`, `unsafe`, `partial`, `opaque` or
`native_decide` occurs anywhere; no recursion is non-structural; no module is
missing or duplicated; all Verbatim blocks balance; all stated counts are
correct. The substantive problems are in categories C and A: the historical
limit layer is never grounded, several premise bundles are never discharged,
and a handful of prose notes contradict the code they describe.

Severity key: high = a false claim or broken construction; medium = a real
gap, misplacement or unsupported claim; low = cosmetic or bookkeeping.

---

## Categories B and C: the Lean itself (most severe first)

1. **Medium-high (C), whole document.** The Lemma I limit interface is never
   grounded. Every theorem whose conclusion is `Ultimate … c`, `Near …`,
   `Vanishes …` or `QuadraticInitialDeflection …` has a hypothesis of the same
   kind: `enclosure_reconstruction` (9612), `ultimate_congr` (9948),
   `triangle_normalized_limit` (9961), `constructed_triangle_limit` (9981),
   `sector_ratio_reconstruction` (1318), `enclosed_gap_vanishes` (1306),
   `polygon_trajectory_defect_vanishes` (3273), `lemmaX_reconstruction`
   (1599, 1630), `constructed_quadratic_bridge` (1506). Grep over the printed
   code finds no unconditional instance of any of these predicates. The
   Magnitudes layer (Lemmas I, III Cor. 4, IX, X, De Motu H4) transports
   limits it is handed and never produces one.

2. **Medium-high (C), lines 3265–3279 and 2662–2789 versus 24285.**
   `PolygonTrajectoryEnclosure` (3265) is never proved for any concrete pair,
   so all four edition theorems for the final step of Proposition I
   (`natp00089_polygon_trajectory_defect_control` 2662,
   `natp00090_…` 2670, 1687 `polygon_trajectory_defect_control` 2728,
   1713 `polygon_trajectory_defect_control` 2786) remain conditional. The one
   genuine result of that shape, `HarmonicPathRegion.D_mesh_tends_zero`
   (24285: the outer content of the polygon/curve region tends to zero), is
   never connected to `Vanishes` or `PolygonTrajectoryEnclosure`; the word
   `Vanishes` does not occur after line 3276. The grounded Cauchy/Value layer
   (`endpoint_cauchy` 6547, `ParallelQuadraticEndpoint.endpointValue_eq`
   24731) and the ungrounded Magnitudes layer never meet.

3. **Medium (B/C), lines 1588–1633.** `Principia1687.LemmaXPremises` bundles
   `lower_limit : Ultimate g lowerTriangle c`, `upper_limit`, `enclosure` and
   `velocity_area`; `lemmaX_reconstruction` (1599) is nothing but the squeeze
   of those fields, and the structure is never instantiated.
   `Principia1713.LemmaXPremises` (1626) has the single field
   `geometry : Principia1687.LemmaXPremises g ratio c`, so the "1713
   reconstruction" (1630) is definitionally the 1687 one; the 1713
   finite/monotone-force clause described in the prose (1513–1519) and
   formalised separately in `MonotoneEnclosure` (1677–1774) is not connected
   to it. `discharges_quadraticPremise_reconstruction` (1607) itself says
   "not a completed historical discharge of Hypothesis 4".

4. **Medium (B/C), lines 1497–1511.** `ContactEnclosure` carries
   `lower_contact`/`upper_contact : Ultimate magnitudes …` and
   `mechanical_enclosure : Near …`; `constructed_quadratic_bridge` (1506)
   concludes `QuadraticInitialDeflection` by squeezing them. The structure is
   never instantiated; its docstring concedes "Establishing these data from
   an actual curved diagram remains open."

5. **Medium (C), lines 19093–19292.** `ForceClasses.Oracle` is introduced as
   "Uniform rational approximations to possibly irrational accelerations"
   (19076), but the only instances are `exactOracle`
   (`error := fun _ => Fraction.ofInt 0`, 19248), `harmonicOracle` (19264) and
   `parallelOracle` (19292). The nonzero-error contract (`error_vanishes`,
   `coherent`) is never discharged by a printed instance, so the whole
   GeneralForce* chain (21484–25003) has only exact rational laws as
   instances.

6. **Medium (C), lines 9308–9345.** `CircleChord.sagitta_chord :
   equiv (mul s (sub (twice r) s)) (quarterOf c)` is used by no theorem;
   `force_ratio_is_sagitta_ratio` (9320) only cross-multiplies `w.s` and
   `w'.s`. The module docstring (9344) nevertheless lists "the exact
   sagitta-chord relation carried by `CircleChord`" as part of "the shared
   checked core".

7. **Medium (C), lines 22314, 22327, 22505.** The GeneralForceGrowth
   docstring says "Singular laws use the annular constructor rather than
   growth at the origin", but no annular `Frame` constructor is printed; the
   only constructor is `ball_frame` with `r = 0` (22522), so the
   `0 < (velocityCap …).num` branch of `inner_zero_or_speed_positive` and the
   `areal_bound` field with `r > 0` (22508–22509) are never exercised.
   `GeneralForceGrowth.Data` (22327, fields `window`, `lipschitz`,
   `ball_contained`) is never instantiated anywhere.

8. **Medium-low (C), lines 15252, 19185, 19191, 19235–19245.**
   `CalibratedGrowth.Growth`, `ForceClasses.ContinuousOn` and `BoundedOn`
   appear only as hypotheses (`run_norm_le_cap` 15447,
   `continuous_local_refinement` 19365, `sampled_polygon_*_bound`
   19330–19360); `ClassBForce` (19239) and `ClassCForce` (19241) are never
   established for any oracle; `def ClassDForce (_o : CentralOracle) : Prop
   := True` (19245) is vacuous.

9. **Low (B), restatement and projection proofs.** `natp00089_*` and
   `natp00090_*` (2628–2676) and the 1687/1713 `finite_equal_areas`,
   `finite_componendo`, `polygon_trajectory_defect_control` (2710–2789) are
   twelve one-line aliases of three theorems (`all_unsigned_cell_areas`,
   `positive_unsigned_area_comparison`, `polygon_trajectory_defect_vanishes`);
   `velocityContact_position`/`impulseContact_position` (2827, 2831) and
   `oneCellMotionRefinementCompatible_start/_end` (3105, 3114) are
   `h.1`/`h.2`; `Principia1713.lemmaX_reconstruction` (1630) is a projection;
   `withinCell_position_bounded` (587) adds two unused hypotheses (`_hr0`,
   `_hrcell`) to `withinCell_position`. Together these inflate the per-item
   theorem counts (Prop I "435 theorems").

10. **Low (B), dead declarations.** `Contact.Quantities` (2037) and
    `PartitionControl.positiveWeights` (3504) are never used; `SeqVanishes`
    (2194) is proved once by `reciprocal_budget_vanishes` (2200) and never
    consumed.

11. **Low (B), `decide` on nested rational schedules with large literals.**
    `sample_two_block_error` 5180 (`⟨173, 256⟩`), `sample_second_error` 7786
    (`⟨545, 65536⟩`), `sample_alias_actual_error` 8272 (`⟨8927, 65536⟩`),
    `three_tick_finite_control` 20043 (`⟨426975, 16777216⟩`).
    Kernel-reducible through Int arithmetic, but heavy.

12. **Low (B), namespace scattering, lines 12272–12476.**
    `BarrowLib/Polygon/DyadicArithmetic.lean` declares into six
    `NewtonLimitDynamics.Polygon.*` namespaces (`PointAlgebra` 10318/10415 and
    `StateDistance` 12505–12538 do the same). For example
    `HarmonicDyadic.neg_equiv`, used at 7010, exists only at 12317 and not in
    the printed `HarmonicDyadic` module, so names cannot be located by module.

13. **None found (B).** No self-referential definition. Every recursion
    (`isum`, `nsum`, `motion`, `schedule`, `swept`, `elapsed`, `ticks`,
    `finiteAddress`, `interval`, `precision`, `errorBudget`, `quadraticCap`,
    `fineBlocks`, `coarseBlocks`, `run`, `sourceBudget`, `fpower`,
    `factorPower`, `pairWeights`, `vel`, `pos`, `tri`) is structural on `Nat`
    or `List`. Every `Quotient.lift`/`liftOn₂` carries its invariance proof.
    `Classical.choose` is confined to `GeneralForcePrecision.threshold`
    (21435), `BoundedCuts.step` (16761) and `SampledValues.admissibleName`
    (17684). Premise bundles that *are* discharged: `EuclideanConstruction` by
    `lattice` (2549); `Magnitudes` by `Fraction.magnitudes` (9772); `Form` by
    `dotForm`/`detForm` (18655, 18664); `Cut` by `rationalCut`/`contentCut`;
    `Cover` by `actualCover`/`emptyCover`/`singletonCover`; `Family` by
    `CompletedForce.family` (23518); `VertexChain` by both `vertices`; `Frame`
    by `ball_frame`; `Conditions` by `HarmonicGeneralEndpoint.conditions`
    (22049) and `GeneralForceGrowth.conditions` (22430); `EndpointCauchyName`
    by every name constructor with a derived `cauchy` proof.

---

## Category A: the document (most severe first)

14. **Medium, line 2094.** `Contact/FiniteSums.lean` is printed under
    Lemma XI although its docstrings are about "Lower rectangles for a linear
    velocity diagram" and "y=x²" step sums (Lemma II/III and Lemma X
    material). It is imported by `Contact/AreaCoefficient.lean`, printed
    earlier under Lemma X (import at 1780), so the "import order" claim is
    also broken.

15. **Medium, line 130, Definition I note.** It says a `mass` parameter
    appears in `Comparison/CircleCompare`; that module has no mass variable
    and its docstring says "no mass, no realized orbit" (9288), while
    `Diagnostic/DeflectionPotential` (`linearPotential (m g : Fraction)`,
    19851) and `Diagnostic/QuadraticEndpointPotential` do carry a mass and are
    not listed.

16. **Medium, lines 2588–2676.** `DeMotu1684/AreaLaw.lean` is counted among
    modules that "cite" 1687 Proposition I, while its docstrings cite only
    NATP00089 and NATP00090 (De Motu). This merges textual stages that the
    project method keeps separate; the rendering is explicitly of the 1687
    edition.

17. **Low-medium, lines 9276 and 9315.** CircleCompare's docstring
    attributes "force as sagitta over `t²`" to Proposition II for the 1687
    route; Proposition II is the converse area theorem and contains no
    force measure, and the rendering's own Prop IV paragraph cites Lemma X,
    Corollary 2.

18. **Low, lines 1477–1479 and 2398.** Lemma IX says "1 theorem in 2 modules
    cite this item" where the second module is the one-line shim
    `NewtonLimitDynamics/Common/RationalMagnitudes.lean`; Prop I's "26
    modules" likewise counts the theorem-free shims `Polygon/PointBounds.lean`
    (4584) and `Polygon/TriangleBounds.lean` (4590), while the sibling shims
    `Common/Quadratic` (25433), `Common/FiniteGrowth` (19056),
    `Polygon/ConvexCover` (19466) and `Polygon/BinaryTime` (19607) are placed
    in Appendix B. The counting and placement rule for shims is
    inconsistent.

19. **Low, lines 451 and 4449.** "In import order" holds only within an
    item: `ZeroForce.lean` (Law I) imports `PartitionControl` (printed under
    Prop I, 3434), and `HarmonicRefinement.lean` (Prop I) imports
    `HarmonicStability` (printed under Prop IV, 9121).

20. **Low, lines 4374–4385.** `CentralSchedule.unequal_cells_converse` is
    "motivated by Proposition II, whose statement speaks of areas
    proportional to times", but Prop II (8496) carries no cross-reference to
    it, contrary to the "How to read" promise at line 66.

21. **Low, line 426, Scholium note.** `Point := Fraction × Fraction` is
    attributed to `TimeSubdivision`; it is defined in
    `BarrowLib/Polygon/PointAlgebra.lean` (10324), merely inside that
    namespace.

22. **Low, line 171, Definition IV note.** The kick
    `pointAdd s.2 (pointScale d (a y))` "at the arrival vertex" is attributed
    to `TimeSubdivision.endKick`, whose kick uses a constant `a` (3298); only
    `CentralSchedule.cell` evaluates the field at the arrival point.

23. **Low, lines 462–463, `ZeroForce.inertialAt` docstring.** It says the
    map "is built from the finite recurrence below; it is not an assumed
    continuum curve", but it is the closed formula
    `pointAdd p (pointScale t v)`; the recurrence is only shown to agree with
    it afterwards (`partitionMotion_zero_force`, 536).

24. **Low (A/C), line 9119, Proposition IV.** Neither the 1687 route
    (Lemma V + Lemma XI) nor the 1713 route (Prop I Cor. 4 + Lemma VII) has
    any Lean beyond the comment at 9328–9345 ("deliberately not derived
    here"). `HarmonicStability` is placed here on the strength of "compare
    Proposition IV Cor. 3" (9131) although its content serves the Prop I
    harmonic modules, and `InverseCubeAreal` is a diagnostic. The item's
    "15 theorems in 3 modules" therefore contains no reconstruction of the
    proposition's proof.

---

## Verified clean

25. **Document mechanics.** 143 `\begin{Verbatim}`/`\end{Verbatim}` pairs
    balanced; 143 module headers, no duplicates; every `import` statement in
    the document resolves to a printed module (only `Std` is external); each
    header's "N theorems, M lines" matches the printed block; Appendix A's
    "2 modules with 4 theorems", Appendix B's "95 modules with 1002 theorems"
    (plus the two root files), Prop I's 435, Lemma X's 15, Lemma XI's 13,
    Law I's 37, Prop II's 12 and Prop III's 17 all sum correctly. All prose
    cross-references other than those listed above resolve to printed names
    (`RelativeMotion.lawI_uniform`, `RelativeMotion.corVI_relative`,
    `Converse.moving_centre_equal_areas_central`,
    `Finite.EuclideanConstruction.kick`, `same_base_parallels`,
    `ForceClasses.parallelOracle`, `Polygon/ParallelQuadraticEndpoint`,
    `CentralSchedule.central`, `CentralOracle.inward`,
    `PolygonTrajectoryEnclosure`, `Near`, `Ultimate`,
    `enclosure_reconstruction`, `Within`, `Vanishes`, `BinaryTime`).
