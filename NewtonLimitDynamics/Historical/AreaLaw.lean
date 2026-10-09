import BarrowLib.Polygon.Finite
import BarrowLib.Polygon.SectorFan
import BarrowLib.Polygon.RadialSector
import BarrowLib.Polygon.MotionSampling
import BarrowLib.Polygon.MotionSectorCover
import BarrowLib.Polygon.MotionCurveCover
import NewtonLimitDynamics.Historical.CompositionOfMotions
import NewtonLimitDynamics.Historical.LemmaIII
import ModernLib.Polygon.PathDefect
import ModernLib.Polygon.GeneralForceArea
import ModernLib.Polygon.GivenTrajectoryArea

/-! Historical result: area_law.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! NATP00089. De Motu Theorem I; finite multiplicity area and derived block comparison; limit remains open. -/
/-! Witness: NATP00089.
Source: docs/m1/NATP00089.xml
SHA-256: b91b58f8d0a79a18eb60d6a715a3952821aff4cdfabbb5a16625ff3e572bbc34
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par8
Anchor URLs: NATP00089.par8 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par8; NATP00089.par9 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par9
Proof-step correspondence: Finite equal-time inertial segments and parallel central deflections preserve the triangle areas; composition sums them. The passage then takes the polygon to a curve, which remains open.
-/
/- LATIN BEGIN NATP00089.par8
Theorema 1. Gyrantia omnia radijs ad centrum ductis areas temporibus proportionales describere.
LATIN END NATP00089.par8 -/
/- LATIN BEGIN NATP00089.par9
Dividatur tempus in partes æquales, et prima temporis parte describat corpus vi insita rectam AB. Idem secunda temporis parte si nil impedireta [note: a Hyp. 1.] rectà pergeret ad [del: [unclear: C] ] c describens lineam Bc æqualem ipsi AB adeo ut radijs AS, BS, cS ad centrum actis confectæ forent æquales areæ ASB, BSc. Verum ubi corpus venit ad B agat vis centripeta impulsu unico sed magno, faciat corpus [del: ] a recta Bc deflectere et pergere in recta BC. Ipsi BS parallela agatur cC occurrens BC in C et completa secunda temporis parte b [note: [del: b Hyp 3] [add: b Lem. 1.] ] corpus reperietur in C. Iunge SC et triangulum SBC ob parallelas SB, Cc æquale erit triangulo SBc atqu adeo etiam triangulo S [del: C] [add: A] B. Simili argumento si vis centripeta successivè agat in C, D, E &c, faciens corpus singulis temporis momentis singulas describere rectas CD, DE, EF &c triangulum S [del: B] CD triangulo SBC et SDE ipsi SCD et SEF ipsi SDE æquale erit. Æqualibus igitur te [del: ] [add: mp] oribus æquales areæ describuntur. Sunto jam hæc triangula numero infinita et infinitè parva, sic, ut singulis temporis momentis singula respondeant triangula, agente vi centripeta sine intermissione, & constabit proposit [del: ] [add: io] .
LATIN END NATP00089.par9 -/

namespace DeMotu1684.AreaLaw
open NewtonLimitDynamics.Polygon NewtonLimitDynamics
variable {Point Impulse : Type}

theorem natp00089_finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

theorem natp00089_finite_block_comparison (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

end DeMotu1684.AreaLaw

/-! NATP00090. De Motu Theorem I; no retrospective proposition numbering. -/
/-! Witness: NATP00090.
Source: docs/m1/NATP00090.xml
SHA-256: 790b468987fd8c7716d9d43197ec3a724f7f581ec8b6ed3998edc191b951f998
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par16
Anchor URLs: NATP00090.par16 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par16; NATP00090.par17 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17
Proof-step correspondence: The abstract finite model remains available. The coordinate reconstruction takes this witness's own Lex 1 inertia and Lex 2 calibrated change as explicit premises, uses its Lemma 1 to locate the next arrival, and derives equal consecutive triangle areas for the actual impulse-then-drift recurrence. Finite dissection gives ordinary sector-union area under explicit elementary area rules, nonnegative orientation and a strict common positive half-plane. A separate conditional reconstruction of the unnumbered exhaustion passage takes a given rational-time state curve, explicit quadratic mechanical remainders, force comparison, finite bounds, a short window and a positive monotone radial chart of its full image. Sample agreement and mesh shrinking are derived; finite geometric enclosure and elementary exhaustion give any assigned rational swept-sector area as time times the initial areal product divided by two. These coordinate and regularity premises are editorial additions, not quotations or hypotheses explicitly stated here. No printed Lemma I/III or printed-edition law supplies the proof. Arbitrary curves, non-rational area existence, patch assembly and unrestricted between-region control for the mechanical polygons remain open; unrestricted historical Theorem 1 is not certified.
Historical dependency ledger for this exact witness:
- NATP00090.Law1 → NATP00090.T1; passage NATP00090.par17; witness 'De motu sphæricorum corporum in fluidis'; URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17; status explicit_dependency; confidence high.
- NATP00090.L1 → NATP00090.T1; passage NATP00090.par17; witness 'De motu sphæricorum corporum in fluidis'; URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00090.par16
Theorema 1. Gyrantia omnia radijs ad centrum ductis areas temporibus proportionales describere.
LATIN END NATP00090.par16 -/
/- LATIN BEGIN NATP00090.par17
Dividatur tempus in partes æquales, et prima temporis parte describat corpus vi insita rectam AB. Idem secunda temporis parte si nil impediret [del: ] a [note: a [del: Hypoth.] [add: Lex] 1.] rectà pergeret ad c describens lineam Bc æqualem ipsi AB adeo ut radijs AS, BS, cS ad centrum actis confectæ forent æquales areæ ASB, BSc. Verum ubi corpus venit ad B agat vis centripeta impulsu unico sed magno, faciat corpus a recta Bc deflectere et pergere in recta BC. Ipsi BS parallela agatur cC occurrens BC in C et completa secunda temporis parte [del: ] b [note: b Lem. 1.] corpus reperietur in C. Iunge SC et triangulum SBC ob parallelas SB, Cc æquale erit triangulo SBc at adeo etiam triangulo SAB. Simili argumento si vis centripeta successivè agat in C, D, E &c faciens corpus singulis temporis momentis singulas describere rectas CD, DE, EF &c triangulum SCD triangulo SBC et SDE ipsi SCD et SEF ipsi SDE æquale erit. Æqualibus igitur temporibus æquales areæ describuntur. Sunto jam hæc triangula numero infinita et infinitè parva, sic, ut singulis temporis momentis singula respondeant triangula, agente vi centripeta sine intermissione, et constabit propositio.
LATIN END NATP00090.par17 -/

namespace DeMotu1684.AreaLaw
open NewtonLimitDynamics.Polygon NewtonLimitDynamics
variable {Point Impulse : Type}

theorem natp00090_finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

theorem natp00090_finite_block_comparison (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

end DeMotu1684.AreaLaw

namespace DeMotu1684.NATP00090.AreaLaw
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision

/-- Drift to the next vertex, then apply the calibrated field impulse
there. No equal-area or polygon/curve-agreement clause is supplied. -/
def mechanicalCell (motion : Point → Point → Fraction → Point)
    (update : Point → Point → Point) (a : CentralSchedule.Field) (h : Fraction)
    (s : Point × Point) : Point × Point :=
  let q := motion s.1 s.2 h
  (q, update s.2 (pointScale h (a q)))

def polygonState (motion : Point → Point → Fraction → Point)
    (update : Point → Point → Point) (a : CentralSchedule.Field) (h : Fraction)
    (s : Point × Point) : Nat → Point × Point :=
  Nat.rec s (fun _ state => mechanicalCell motion update a h state)

def polygonVertex (motion : Point → Point → Fraction → Point)
    (update : Point → Point → Point) (a : CentralSchedule.Field) (h : Fraction)
    (s : Point × Point) (n : Nat) : Point :=
  (polygonState motion update a h s n).1

/-- NATP00090's own Lemma 1 locates C in its AB, Bc, BC construction.
The central impulse and preceding Lex 1 drift then give equal triangles.
The conclusion is a finite signed doubled-area equality. -/
theorem two_triangle_step
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : DeMotu1684.NATP00090.Laws.InertialMotion motion)
    (hII : DeMotu1684.NATP00090.Laws.CalibratedChange update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (p v : Point) (h : Fraction) (hh : 0 ≤ h.num) :
    Fraction.equiv
      (det (motion p v h)
        (motion (motion p v h) (update v (pointScale h (a (motion p v h)))) h))
      (det p (motion p v h)) := by
  let q := motion p v h
  let j := pointScale h (a q)
  have hlemma := DeMotu1684.Composition.natp00090_lemma1_from_laws
    motion update hI hII q v j h hh
  have hj : Fraction.equiv (det q j) (Fraction.ofInt 0) :=
    Fraction.equiv_trans (det_scale_right h q (a q))
      (Fraction.equiv_trans (Fraction.mul_equiv_left h (ha q)) (Fraction.mul_zero h))
  have hd : Fraction.equiv (det q (Parallelogram.diagonal q (pointScale h v) (pointScale h j)))
      (Fraction.add (Fraction.mul h (det q v)) (Fraction.mul h (det q j))) := by
    simp only [Parallelogram.diagonal,TimeSubdivision.det,pointAdd,pointScale,Fraction.equiv,
      Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf
    omega
  have hnext : Fraction.equiv (det q (motion q (update v j) h))
      (Fraction.mul h (det q v)) :=
    Fraction.equiv_trans (det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ hlemma)
      (Fraction.equiv_trans hd (Fraction.equiv_trans
        (Fraction.add_equiv_left _ (Fraction.equiv_trans (Fraction.mul_equiv_left h hj)
          (Fraction.mul_zero h))) (Fraction.add_zero _)))
  have hprior : Fraction.equiv (det p q) (Fraction.mul h (det p v)) :=
    Fraction.equiv_trans (det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI p v h hh))
      (CentralSchedule.det_cell_area p v h)
  have hdrift : Fraction.equiv (det q v) (det p v) :=
    Fraction.equiv_trans (det_congr (hI p v h hh)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) (CentralSchedule.det_drift p v h)
  exact Fraction.equiv_trans hnext
    (Fraction.equiv_trans (Fraction.mul_equiv_left h hdrift) (Fraction.equiv_symm hprior))

/-- Every consecutive triangle of the actual finite recurrence has the
initial triangle's area; the equality is derived from the two-triangle step. -/
theorem polygon_triangle_equal
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : DeMotu1684.NATP00090.Laws.InertialMotion motion)
    (hII : DeMotu1684.NATP00090.Laws.CalibratedChange update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (h : Fraction) (hh : 0 ≤ h.num) (s : Point × Point) (n : Nat) :
    Fraction.equiv
      (det (polygonVertex motion update a h s n) (polygonVertex motion update a h s (n+1)))
      (Fraction.mul h (CentralSchedule.momentum s)) := by
  induction n with
  | zero =>
    exact Fraction.equiv_trans
      (det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI s.1 s.2 h hh))
      (CentralSchedule.det_cell_area s.1 s.2 h)
  | succ n ih =>
    exact Fraction.equiv_trans
      (two_triangle_step motion update hI hII a ha
        (polygonState motion update a h s n).1 (polygonState motion update a h s n).2 h hh) ih

/-- Finite ordinary sector-union area is elapsed time times the initial
areal product divided by two. Common half-plane and nonnegative orientation
are explicit: winding triangles cannot be counted as a simple union. The
area convention is supplied; the curved-sector limit is not proved here. -/
theorem finite_geometric_sector (area : SectorFan.AreaRules)
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : DeMotu1684.NATP00090.Laws.InertialMotion motion)
    (hII : DeMotu1684.NATP00090.Laws.CalibratedChange update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (h : Fraction) (hh : 0 ≤ h.num) (s : Point × Point)
    (hs : 0 ≤ (CentralSchedule.momentum s).num) (n : Nat)
    (hp : ∀ i, i ≤ n → 0 < (polygonVertex motion update a h s i).1.num) :
    area.HasArea (SectorFan.Region (polygonVertex motion update a h s) n)
      (Fraction.mul (BoundedIteration.time h n) (CentralSchedule.momentum s)).half := by
  have htriangle := polygon_triangle_equal motion update hI hII a ha h hh s
  have hregion := SectorFan.region_area area _ n hp (fun i _ =>
    Fraction.nonnegative_equiv (htriangle i) (Fraction.nonnegative_mul _ _ hh hs))
  apply area.congr_value _ _ _ ?_ hregion
  apply Fraction.equiv_trans
    (PolygonFanArea.sum_congr _ _ (fun i => RationalIntervals.half_equiv (htriangle i)) n)
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant (Fraction.mul h (CentralSchedule.momentum s)).half n)
  simp only [BoundedIteration.time,Fraction.equiv,Fraction.half,Fraction.mul,Fraction.ofInt]
  ac_nf

/-- The canonical realization of this witness's recurrence is the same
finite drift/kick polygon used by the elementary comparison estimates. -/
theorem canonical_polygon_eq_run (a : CentralSchedule.Field) (h : Fraction)
    (s : Point × Point) (n : Nat) :
    polygonState ZeroForce.inertialAt pointAdd a h s n = BoundedIteration.run a h s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change mechanicalCell ZeroForce.inertialAt TimeSubdivision.pointAdd a h
      (polygonState ZeroForce.inertialAt TimeSubdivision.pointAdd a h s n) =
      FiniteEstimates.cell a h (BoundedIteration.run a h s n)
    rw [ih]
    rfl

/-- The finite fan law is derived through this witness's own Lemma 1 and
Lex 1/2 chain. The given curve does not supply its area law. -/
theorem canonical_fan_law (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (T : Fraction) (hT : 0 ≤ T.num) (s : Point × Point) (j : Nat) :
    Fraction.equiv (PolygonFanArea.fan
      (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) s k).1)
      (HarmonicDyadic.blocks j)) (Fraction.mul T (CentralSchedule.momentum s)) := by
  have hI : DeMotu1684.NATP00090.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : DeMotu1684.NATP00090.Laws.CalibratedChange pointAdd :=
    pointSub_add_self_left_equiv
  have ht (k : Nat) := polygon_triangle_equal ZeroForce.inertialAt pointAdd hI hII
    a ha (HarmonicDyadic.duration T j) hT s k
  simp only [polygonVertex,canonical_polygon_eq_run] at ht
  apply Fraction.equiv_trans (PolygonFanArea.sum_congr _ _ ht (HarmonicDyadic.blocks j))
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant _ _)
  exact Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))
    (Fraction.mul_equiv_right _ (HarmonicDyadic.blocks_duration T j))

/-- Direct geometric exhaustion for the unnumbered limit passage. Finite
strip arithmetic and a shrinking mesh imply the actual chord-area error
vanishes. No printed historical lemma is used or attributed to De Motu. -/
theorem radial_chord_errors_vanish (area : SectorFan.AreaRules)
    (g : Fraction → Fraction) (l r A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (hg : MonotoneRectangles.MonotoneOn g l r) (hbase : 0 < (g l).num)
    (hA : area.HasArea (RadialSector.sector g l r) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun j => MonotoneRectangles.maxWidth (parts j))) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun j => (HarmonicTimeComparison.durationDifference A
        (RadialSector.chordArea g (parts j))).abs) :=
  RadialSector.chord_errors_vanish area g parts hg hbase A hA
    (MonotoneRectangles.gaps_vanish (RadialSector.density g) parts
      (RadialSector.density_monotone g l r hg (Int.le_of_lt hbase)) hmesh)

/-- Conditional local area law for the full image of a given rational-time
curve. The supplied mechanical remainder, bounds, chart and geometric area
convention are stated separately from existence. Polygon/sample agreement
and mesh exhaustion are conclusions. The final constant-discrepancy
comparison is constructed, not supplied as a curve-limit premise.

This is an editorial reconstruction of NATP00090's unnumbered assertion,
using its own finite law chain and elementary exhaustion. Its compiled proof
uses no printed-edition theorem. General curve
and non-rational scope and mechanical between-region B remain open. -/
theorem sampled_radial_sector_area (area : SectorFan.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : MotionSampling.Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u)
    (A : Fraction) (hA : area.HasArea (MotionSampling.sweptSector u T) A) :
    Fraction.equiv A (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half := by
  let K := (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half
  let F := fun j => PolygonFanArea.fan
    (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1)
    (HarmonicDyadic.blocks j)
  let Q := fun j => PolygonFanArea.fan
    (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j)
  let chord := fun j => RadialSector.chordArea g (parts j)
  have hmesh := MotionSampling.sampled_radial_mesh a C T L B P V u d g l r parts chart
  have hAradial := area.congr_set _ _ A (MotionSampling.charted_sector g l r T parts u chart) hA
  have hgeom := radial_chord_errors_vanish area g l r A parts
    chart.monotone chart.positive hAradial hmesh
  have hfan := MotionSampling.sampled_fan_comparison a C T L B P V u d
  have hfinite (j : Nat) : Fraction.equiv
      (SectorFan.areaSum
        (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1)
        (HarmonicDyadic.blocks j)) K :=
    Fraction.equiv_trans (MotionSampling.areaSum_half_fan _ _)
      (RationalIntervals.half_equiv (canonical_fan_law a ha T d.time_nonnegative _ j))
  have hchord (j : Nat) : Fraction.le (HarmonicTimeComparison.durationDifference K (chord j)).abs
      (HarmonicTimeComparison.durationDifference (F j) (Q j)).abs :=
    Fraction.le_equiv_left (Fraction.abs_equiv (HarmonicTimeComparison.difference_congr
      (Fraction.equiv_symm (hfinite j))
      (Fraction.equiv_symm (MotionSampling.sampled_chord_area g l r T parts u chart j))))
      (MotionSampling.areaSum_error_le_fan_error _ _ _)
  let D := (HarmonicTimeComparison.durationDifference K A).abs
  have hbound (j : Nat) : Fraction.le D (Fraction.add
      (HarmonicTimeComparison.durationDifference (F j) (Q j)).abs
      (HarmonicTimeComparison.durationDifference A (chord j)).abs) :=
    Fraction.magnitudes.le_trans (MotionSampling.difference_triangle K (chord j) A)
      (Fraction.add_le_add (hchord j)
        (Fraction.le_of_equiv (HarmonicTimeRealization.durationDifference_abs_symm (chord j) A)))
  have hsmall := MotionSampling.vanishing_add _ _ hfan hgeom
  have hDsmall : Exhaustion.VanishingDifference Fraction.magnitudes (fun _ => D) := by
    intro eps heps
    obtain ⟨N,hN⟩ := hsmall eps heps
    exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (hbound j) (hN j hj)⟩
  have hzero := Exhaustion.rational_terminal_zero (fun _ => D) D
    (Fraction.abs_num_nonnegative _) hDsmall (fun _ _ hd => ⟨0,fun _ _ => hd⟩)
  exact Fraction.equiv_symm (MotionSampling.equiv_of_abs_difference_zero K A hzero)

/-- Swept areas for two admissible windows of one given curve sharing
their initial time compare as those durations. The conditional local
chart/regularity/area scope of the preceding theorem is retained. -/
theorem sampled_radial_sector_comparison (area : SectorFan.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (C T₁ T₂ L B P V : Fraction) (u : Fraction → Point × Point)
    (d₁ : MotionSampling.Conditions a C T₁ L B P V u)
    (d₂ : MotionSampling.Conditions a C T₂ L B P V u)
    (g₁ g₂ : Fraction → Fraction) (l₁ r₁ l₂ r₂ : Fraction)
    (parts₁ : Nat → MonotoneRectangles.Partition l₁ r₁)
    (parts₂ : Nat → MonotoneRectangles.Partition l₂ r₂)
    (chart₁ : MotionSampling.RadialChart g₁ l₁ r₁ T₁ parts₁ u)
    (chart₂ : MotionSampling.RadialChart g₂ l₂ r₂ T₂ parts₂ u)
    (A₁ A₂ : Fraction) (hA₁ : area.HasArea (MotionSampling.sweptSector u T₁) A₁)
    (hA₂ : area.HasArea (MotionSampling.sweptSector u T₂) A₂) :
    Fraction.equiv (Fraction.mul A₁ T₂) (Fraction.mul A₂ T₁) := by
  have h₁ := sampled_radial_sector_area area a ha C T₁ L B P V u d₁
    g₁ l₁ r₁ parts₁ chart₁ A₁ hA₁
  have h₂ := sampled_radial_sector_area area a ha C T₂ L B P V u d₂
    g₂ l₂ r₂ parts₂ chart₂ A₂ hA₂
  apply Fraction.equiv_trans (Fraction.mul_equiv_right T₂ h₁)
  apply Fraction.equiv_trans (b := Fraction.mul
    (Fraction.mul T₂ (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half T₁)
  · simp only [Fraction.equiv,Fraction.mul,Fraction.half]
    ac_nf
  · exact Fraction.mul_equiv_right T₁ (Fraction.equiv_symm h₂)


/-- This witness's actual canonical mechanical polygon and the sample-chord
polygon have derived edge bounds and a shrinking cover of their matched
finite locus. This coordinate intermediary supplies no full-curve agreement,
assigned union area or between-region B. Its quantitative statement is an
editorial derivation from the explicit motion premises. -/
theorem mechanical_sampled_chord_control (a : CentralSchedule.Field) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u) :
    (∀ j k, k < HarmonicDyadic.blocks j → ∀ theta, ConvexCover.UnitInterval theta →
      Fraction.le (FiniteEstimates.pointDistance
        (ConvexCover.lerp theta
          (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
            (u (Fraction.ofInt 0)) k)
          (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
            (u (Fraction.ofInt 0)) (k+1)))
        (ConvexCover.lerp theta (MotionSampling.samples u T j k).1
          (MotionSampling.samples u T j (k+1)).1)) (MotionSampling.stateBudget C T j)) ∧
    (∀ j x, ConvexCover.MatchedRegion
      (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)))
      (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j) x →
      ConvexCover.SquareCover (fun k => (MotionSampling.samples u T j k).1)
        (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes (MotionSampling.chordCoverBudget C T V) := by
  refine ⟨?_,?_,MotionSampling.chord_cover_budgets_vanish C T V
    d.remainder_nonnegative d.time_nonnegative d.velocity_nonnegative⟩
  · intro j k hk theta htheta
    simp only [polygonVertex,canonical_polygon_eq_run]
    exact MotionSampling.sampled_chord_edge_bound a C T L B P V u d j k hk theta htheta
  · intro j x
    have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)) = fun k =>
        (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
      funext k
      exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
    rw [hp]
    exact MotionSampling.sampled_chord_cover a C T L B P V u d j x

/-- The independent-parameter finite edge strip has the same cover budget.
Source: this editorial coordinate consequence of the motion premises and this
witness's own canonical polygon identity. Sector-difference inclusion is not
assumed or concluded. -/
theorem mechanical_filled_chord_control (a : CentralSchedule.Field) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u) :
    (∀ j x, ConvexCover.FilledRegion
      (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)))
      (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j) x →
      ConvexCover.SquareCover (fun k => (MotionSampling.samples u T j k).1)
        (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes (MotionSampling.chordCoverBudget C T V) := by
  refine ⟨?_,MotionSampling.chord_cover_budgets_vanish C T V
    d.remainder_nonnegative d.time_nonnegative d.velocity_nonnegative⟩
  intro j x
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp]
  exact MotionSampling.sampled_filled_cover a C T L B P V u d j x

/-- The motion estimates and positive chart derive the finite polygons'
half-plane premise eventually. This witness's own mechanical triangle chain
then assigns the actual sector-union area. Source: this editorial derivation;
the regularity/chart premises are not quotations from Newton. No B or
arbitrary-time polygon agreement is concluded. -/
theorem eventual_mechanical_sector_area (area : SectorFan.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ N, ∀ j, N ≤ j →
      area.HasArea (SectorFan.Region
        (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))) (HarmonicDyadic.blocks j))
        (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half := by
  obtain ⟨N,hN⟩ := MotionSampling.polygon_eventually_positive a C T L B P V u d g l r parts chart
  refine ⟨N,fun j hj => ?_⟩
  have hI : DeMotu1684.NATP00090.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : DeMotu1684.NATP00090.Laws.CalibratedChange TimeSubdivision.pointAdd :=
    TimeSubdivision.pointSub_add_self_left_equiv
  have hp : ∀ k, k ≤ HarmonicDyadic.blocks j →
      0 < (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)) k).1.num := by
    intro k hk
    simp only [polygonVertex,canonical_polygon_eq_run]
    exact hN j hj k hk
  exact area.congr_value _ _ _
    (RationalIntervals.half_equiv (Fraction.mul_equiv_right _
      (HarmonicDyadic.blocks_duration T j)))
    (finite_geometric_sector area ZeroForce.inertialAt TimeSubdivision.pointAdd hI hII a ha
      (HarmonicDyadic.duration T j) d.time_nonnegative (u (Fraction.ofInt 0)) hs
      (HarmonicDyadic.blocks j) hp)


/-- This witness's own finite triangle chain derives the mechanical
orientation. The motion estimates and full positive radial chart then derive
a square/terminal-triangle cover of the mechanical/sample sector-union
symmetric difference eventually. Source: this editorial finite-coordinate
consequence; no difference area, B for the given curve, or arbitrary-time
polygon agreement is assumed or concluded. -/
theorem eventual_mechanical_sector_difference_cover
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ N, ∀ j, N ≤ j →
      let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0))
      let q := fun k => (MotionSampling.samples u T j k).1
      ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧
          ¬ SectorFan.Region q (HarmonicDyadic.blocks j) x) ∨
        (SectorFan.Region q (HarmonicDyadic.blocks j) x ∧
          ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
        ConvexCover.SquareCover q (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x ∨
          SectorFan.Triangle (p (HarmonicDyadic.blocks j)) (q (HarmonicDyadic.blocks j)) x := by
  have hI : DeMotu1684.NATP00090.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : DeMotu1684.NATP00090.Laws.CalibratedChange TimeSubdivision.pointAdd :=
    TimeSubdivision.pointSub_add_self_left_equiv
  have hdet : ∀ j k, k < HarmonicDyadic.blocks j → 0 ≤ (TimeSubdivision.det
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num := by
    intro j k _
    have he := polygon_triangle_equal ZeroForce.inertialAt TimeSubdivision.pointAdd hI hII a ha
      (HarmonicDyadic.duration T j) d.time_nonnegative (u (Fraction.ofInt 0)) k
    have he' := he
    simp only [polygonVertex,canonical_polygon_eq_run] at he'
    exact Fraction.nonnegative_equiv he'
      (Fraction.nonnegative_mul _ _ d.time_nonnegative hs)
  obtain ⟨N,hN⟩ := MotionSampling.eventual_sampled_sector_difference_cover a C T L B P V u d
    g l r parts chart hdet
  refine ⟨N,fun j hj => ?_⟩
  dsimp only
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp]
  exact hN j hj



/-- This witness's own sector-difference inclusion is enclosed by one
finite square union, including its terminal triangle. Its nonnegative
assigned area and vanishing bound are derived under the explicit existing
translation-and-cut area convention. Source: this editorial coordinate
consequence; neither the actual difference's area nor the given curve's B
is constructed, and no new hypothesis is attributed to Newton's text. -/
theorem eventual_mechanical_sector_difference_cover_areas
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (MotionSectorCover.cover a C T B V u j) (A j) ∧
        0 ≤ (A j).num ∧
        Fraction.le (A j) (MotionSectorCover.budget C T B V (u (Fraction.ofInt 0)) j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A ∧
      ∃ N, ∀ j, N ≤ j →
        let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))
        let q := fun k => (MotionSampling.samples u T j k).1
        ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧
            ¬ SectorFan.Region q (HarmonicDyadic.blocks j) x) ∨
          (SectorFan.Region q (HarmonicDyadic.blocks j) x ∧
            ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
          MotionSectorCover.cover a C T B V u j x := by
  obtain ⟨A,hA,hvanish⟩ := MotionSectorCover.cover_areas area a C T B V u
    d.remainder_nonnegative d.time_nonnegative d.force_nonnegative d.velocity_nonnegative
  obtain ⟨N,hN⟩ := eventual_mechanical_sector_difference_cover a ha C T L B P V u d hs
    g l r parts chart
  refine ⟨A,hA,hvanish,N,fun j hj => ?_⟩
  dsimp only
  intro x hx
  rcases hN j hj x hx with h | h
  · exact MotionSectorCover.edge_cover_inside a C T B V u j d.remainder_nonnegative
      d.time_nonnegative d.force_nonnegative x h
  · apply MotionSectorCover.terminal_cover_inside a C T L B P V u d j x
    simpa only [polygonVertex,canonical_polygon_eq_run] using! h


/-- This witness's own mechanical/sample-sector cover is combined with the
derived collar of the full given curve and its chord polygon. The resulting
finite square union has a constructed nonnegative area tending to zero.
Source: this editorial finite-coordinate consequence of the explicitly
stated motion, chart and translation/cut premises. No between-region area
or arbitrary-time polygon/curve agreement is supplied or constructed. -/
theorem eventual_mechanical_curve_between_cover_areas
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (MotionCurveCover.cover a C T B P V u g l r chart.positive j) (A j) ∧
        0 ≤ (A j).num ∧ Fraction.le (A j)
          (MotionCurveCover.budget C T B P V (u (Fraction.ofInt 0)) g l r chart.positive j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A ∧
      ∃ N, ∀ j, N ≤ j →
        let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))
        ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧ ¬ MotionSampling.sweptSector u T x) ∨
          (MotionSampling.sweptSector u T x ∧ ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
          MotionCurveCover.cover a C T B P V u g l r chart.positive j x := by
  obtain ⟨A,hA,hvanish⟩ := MotionCurveCover.cover_areas area a C T B P V u g l r chart.positive
    (MotionCurveCover.chart_terminal_nonnegative g l r T parts u chart)
    d.remainder_nonnegative d.time_nonnegative d.force_nonnegative d.position_nonnegative d.velocity_nonnegative
  obtain ⟨_,_,_,N,hN⟩ := eventual_mechanical_sector_difference_cover_areas area a ha
    C T L B P V u d hs g l r parts chart
  refine ⟨A,hA,hvanish,N,fun j hj => ?_⟩
  dsimp only
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  have hN' := hN j hj
  dsimp only at hN'
  rw [hp] at hN' ⊢
  exact MotionCurveCover.between_cover_of_sector_cover a C T L B P V u d g l r parts chart j hN'

/-- Any separately assigned rational areas of the actual mechanical/curve
sector symmetric differences are nonnegative and vanish. The cover and
exhaustion are conclusions; existence of these between-region areas remains
an explicit premise, separate from existence of the given trajectory. -/
theorem mechanical_between_area_approximation
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u)
    (D : Nat → Fraction) (hD : ∀ j, area.HasArea (MotionCurveCover.between a T u j) (D j)) :
    (∀ j, 0 ≤ (D j).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes D := by
  apply MotionCurveCover.assigned_between_areas_vanish_of_cover area a C T L B P V u d
    g l r parts chart D hD
  obtain ⟨_,_,_,N,hN⟩ := eventual_mechanical_curve_between_cover_areas area a ha
    C T L B P V u d hs g l r parts chart
  refine ⟨N,fun j hj => ?_⟩
  have hN' := hN j hj
  dsimp only at hN'
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp] at hN'
  exact hN'

end DeMotu1684.NATP00090.AreaLaw

/-! 1687. Proposition I finite construction and conditional local rational swept-sector law; unrestricted theorem open. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par44
Anchor URLs: NATP00077.par44 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par44; NATP00077.par45 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45
Proof-step correspondence: The edition's Laws Corollary I is actually used with supplied inertia/additive-change predicates to construct the next vertex and derive equal triangles. Finite composition and radial separation identify ordinary local triangle-union area under explicit area rules. A positive monotone radial sector and its actual chord polygon have derived shrinking area errors and between-region covers, using the edition's Lemmas III/I. A further conditional given-motion reconstruction derives finite sample agreement and mesh exhaustion from explicit quadratic remainders and bounds, then proves the assigned local rational swept-sector area proportional to time. Global/non-rational scope and existence of the between-region area for the mechanical polygons remain open; full Proposition I is not certified.
Historical dependency ledger for this exact witness:
- P1687.Law1 → P1687.P1; passage NATP00077.par45; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status explicit_dependency; confidence high.
- P1687.Composition → P1687.P1; passage NATP00077.par45; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status explicit_dependency; confidence high.
- P1687.L3C4 → P1687.P1; passage NATP00077.par45; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status explicit_dependency; confidence high.
- P1687.L3 → P1687.P1; passage NATP00077.par45 (the quoted Corollary IV curve-limit step); witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status editorial_interpretation; confidence high. The radial triangle exhaustion below applies Lemma III arithmetic in a new coordinate reconstruction, not as an additional explicit Newton citation.
- NATP00089.T1 → P1687.P1; passage NATP00077.par45; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status editorial_interpretation; confidence high.
-/
/- LATIN BEGIN NATP00077.par44
Areas quas corpora in gyros acta radiis ad immobile centrum virium ductis describunt, & in planis immobilibus consistere, & esse temporibus proportionales.
LATIN END NATP00077.par44 -/
/- LATIN BEGIN NATP00077.par45
Dividatur tempus in partes æquales, & prima temporis parte describat corpus vi insita rectam AB. Idem secunda temporis parte, si nil impediret, recta pergeret ad c, (per Leg. I) describens lineam Bc æqualem ipsi AB, adeo ut radiis AS, BS, cS ad centrum actis, confectæ forent æquales areæ ASB, BSc. Verum ubi corpus venit ad B, agat viscentripeta impulsu unico sed magno, faciatq; corpus a recta Bc deflectere & pergere in recta BC. Ipsi BS parallela agatur cC occurrens BC in C, & completa secunda temporis parte, corpus (per Legum Corol. 1) reperietur in C, in eodem plano cum triangulo ASB. Junge SC, & triangulum SBC, ob parallelas SB, Cc, æquale erit triangulo SBc, atq; adeo etiam triangulo SAB. Simili argumento si vis centripeta successive agat in C, D, E, &c. faciens ut corpus singulis temporis particulis singulas describat rectas CD, DE EF, &c. jacebunt hæ in eodem plano, & triangulum SCD triangulo SBC & SDE ipsi SCD & SEF ipsi SDE æquale erit. Æqualibus igitur temporibus æquales areæ in plano immoto describuntur: & componendo, sunt arearum summæ quævis SADS, SAFS inter se, ut sunt tempora descriptionum. Augeatur jam numerus & minuatur latitudo triangulorum in infinitum, & eorum ultima perimeter ADF, (per Corollarium quartum Lemmatis tertii) erit linea curva; adeoq; vis centripeta qua corpus de tangente hujus curvæ perpetuo retrahitur, aget indesinenter; areæ vero quævis descriptæ SADS, SAFS temporibus descriptionum semper proportionales, erunt iisdem temporibus in hoc casu proportionales. Q.E.D.
LATIN END NATP00077.par45 -/

namespace Principia1687.PropositionI
open NewtonLimitDynamics.Polygon NewtonLimitDynamics
variable {Point Impulse : Type}

theorem finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

theorem finite_componendo (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

/-! Coordinate realization of the finite historical construction. Inertia
governs each drift and the directed impulse changes its arrival velocity.
The laws are independent mechanical premises; equality of triangle areas
and identification with a local geometric union are proved below. -/

def mechanicalCell
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) : TimeSubdivision.Point × TimeSubdivision.Point :=
  let q := motion s.1 s.2 h
  (q, update s.2 (TimeSubdivision.pointScale h (a q)))

def polygonState
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) : Nat → TimeSubdivision.Point × TimeSubdivision.Point :=
  Nat.rec s (fun _ state => mechanicalCell motion update a h state)

def polygonVertex
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) : TimeSubdivision.Point :=
  (polygonState motion update a h s n).1

open TimeSubdivision in
/-- Newton's AB, Bc, BC step: the edition's Laws Corollary I locates C;
the central direction and the preceding Law I drift give equal triangles.
Neither equal areas nor an areal-product conservation law is a premise. -/
theorem two_triangle_step
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1687.Laws.InertialMotion motion)
    (hII : Principia1687.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (p v : TimeSubdivision.Point) (h : Fraction) :
    Fraction.equiv
      (TimeSubdivision.det (motion p v h)
        (motion (motion p v h) (update v (pointScale h (a (motion p v h)))) h))
      (TimeSubdivision.det p (motion p v h)) := by
  let q := motion p v h
  let j := pointScale h (a q)
  have hcor := Principia1687.Laws.corollary1_from_laws motion update hI hII q v j h
  have hj : Fraction.equiv (TimeSubdivision.det q j) (Fraction.ofInt 0) :=
    Fraction.equiv_trans (det_scale_right h q (a q))
      (Fraction.equiv_trans (Fraction.mul_equiv_left h (ha q)) (Fraction.mul_zero h))
  have hd : Fraction.equiv (TimeSubdivision.det q (Parallelogram.diagonal q (pointScale h v) (pointScale h j)))
      (Fraction.add (Fraction.mul h (TimeSubdivision.det q v)) (Fraction.mul h (TimeSubdivision.det q j))) := by
    simp only [Parallelogram.diagonal,TimeSubdivision.det,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf
    omega
  have hnext : Fraction.equiv
      (TimeSubdivision.det q (motion q (update v j) h))
      (Fraction.mul h (TimeSubdivision.det q v)) :=
    Fraction.equiv_trans (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ hcor)
      (Fraction.equiv_trans hd (Fraction.equiv_trans
        (Fraction.add_equiv_left _ (Fraction.equiv_trans (Fraction.mul_equiv_left h hj)
          (Fraction.mul_zero h))) (Fraction.add_zero _)))
  have hprior : Fraction.equiv (TimeSubdivision.det p q)
      (Fraction.mul h (TimeSubdivision.det p v)) :=
    Fraction.equiv_trans
      (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI p v h))
      (CentralSchedule.det_cell_area p v h)
  have hdrift : Fraction.equiv (TimeSubdivision.det q v) (TimeSubdivision.det p v) :=
    Fraction.equiv_trans (TimeSubdivision.det_congr (hI p v h)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) (CentralSchedule.det_drift p v h)
  exact Fraction.equiv_trans hnext
    (Fraction.equiv_trans (Fraction.mul_equiv_left h hdrift) (Fraction.equiv_symm hprior))

theorem polygon_triangle_equal
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1687.Laws.InertialMotion motion)
    (hII : Principia1687.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) :
    Fraction.equiv
      (TimeSubdivision.det (polygonVertex motion update a h s n) (polygonVertex motion update a h s (n+1)))
      (Fraction.mul h (CentralSchedule.momentum s)) := by
  induction n with
  | zero =>
    exact Fraction.equiv_trans
      (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI s.1 s.2 h))
      (CentralSchedule.det_cell_area s.1 s.2 h)
  | succ n ih =>
    exact Fraction.equiv_trans
      (two_triangle_step motion update hI hII a ha
        (polygonState motion update a h s n).1 (polygonState motion update a h s n).2 h) ih

/-- The historical finite construction now has an actual local sector-union
area, rather than only a multiplicity-counted fan sum. The half-plane and
area convention are explicit geometric premises; this is not the curved
trajectory or the limiting step of Proposition I. -/
theorem finite_geometric_sector
    (area : SectorFan.AreaRules)
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1687.Laws.InertialMotion motion)
    (hII : Principia1687.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (h : Fraction) (hh : 0 ≤ h.num)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hs : 0 ≤ (CentralSchedule.momentum s).num)
    (n : Nat) (hp : ∀ i, i ≤ n → 0 < (polygonVertex motion update a h s i).1.num) :
    area.HasArea (SectorFan.Region (polygonVertex motion update a h s) n)
      (Fraction.mul (BoundedIteration.time h n) (CentralSchedule.momentum s)).half := by
  have htriangle := polygon_triangle_equal motion update hI hII a ha h s
  have hregion := SectorFan.region_area area _ n hp (fun i _ =>
    Fraction.nonnegative_equiv (htriangle i) (Fraction.nonnegative_mul _ _ hh hs))
  apply area.congr_value _ _ _ ?_ hregion
  apply Fraction.equiv_trans
    (PolygonFanArea.sum_congr _ _ (fun i => RationalIntervals.half_equiv (htriangle i)) n)
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant (Fraction.mul h (CentralSchedule.momentum s)).half n)
  simp only [BoundedIteration.time,Fraction.equiv,Fraction.half,Fraction.mul,Fraction.ofInt]
  ac_nf

/-! Local curved-sector exhaustion, in rational coordinates. The given
positive monotone radial graph and its actual chord polygon have derived
geometric enclosures. This applies the edition's Lemma III to radial triangle
areas; it is our reconstruction of an area-limit step, not a quotation of
Newton's rectangle construction. Assigned rational areas and the partial
area convention remain premises. The mesh is in the slope parameter, not yet the equal-time
mechanical polygon's mesh. No force-polygon/curve agreement is assumed or
proved by these geometric declarations. -/
theorem radial_sector_approximation (area : RadialSector.DifferenceAreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 < (g a).num)
    (hA : area.HasArea (RadialSector.sector g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, area.HasArea (RadialSector.chordFigure g (parts m)) (RadialSector.chordArea g (parts m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (RadialSector.chordArea g (parts m))).abs) ∧
    (∀ m x, RadialSector.between g (parts m) x → RadialSector.collar g (parts m) x) ∧
    (∀ m, area.HasArea (RadialSector.collar g (parts m)) (MonotoneRectangles.gap (RadialSector.density g) (parts m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.gap (RadialSector.density g) (parts m)) := by
  have hgap := Principia1687.LemmaIII.unequal_width_gap_vanishes (RadialSector.density g) a b parts
    (RadialSector.density_monotone g a b hg (Int.le_of_lt hbase)) hmesh
  exact ⟨fun m => RadialSector.chord_area area.toSectorAreaRules g (parts m) hg hbase,
    RadialSector.chord_errors_vanish area.toSectorAreaRules g parts hg hbase A hA hgap,
    fun m => RadialSector.between_subset_collar g (parts m) hg hbase,
    fun m => RadialSector.collar_area area g (parts m) hg hbase,hgap⟩

/-- The region between the actual curve and its chord polygon has shrinking
explicit covers above. For any separately assigned rational areas of these
regions, nonnegativity and vanishing are derived, not supplied. -/
theorem radial_between_area_approximation (area : RadialSector.DifferenceAreaRules)
    (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 < (g a).num)
    (B : Nat → Fraction) (hB : ∀ m, area.HasArea (RadialSector.between g (parts m)) (B m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, 0 ≤ (B m).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes B :=
  RadialSector.between_areas_vanish area g parts hg hbase B hB
    (Principia1687.LemmaIII.unequal_width_gap_vanishes (RadialSector.density g) a b parts
      (RadialSector.density_monotone g a b hg (Int.le_of_lt hbase)) hmesh)

/-- Lemma I excludes a positive terminal chord-area discrepancy after the
actual geometric exhaustion. The supplied terminal comparisons do not
construct a terminal value. -/
theorem radial_ultimate_chord_difference_zero (area : RadialSector.DifferenceAreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 < (g a).num)
    (hA : area.HasArea (RadialSector.sector g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (D : Fraction) (hD : 0 ≤ D.num)
    (hterminal : Exhaustion.TerminalLower Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (RadialSector.chordArea g (parts m))).abs) D) :
    Fraction.equiv D (Fraction.ofInt 0) :=
  Principia1687.LemmaI.ultimate_difference_zero _ D hD
    (radial_sector_approximation area g a b A parts hg hbase hA hmesh).2.1 hterminal

/-- The coordinate realization of this edition's mechanical polygon is the
same finite drift/kick recurrence used by the comparison estimates. -/
theorem canonical_polygon_eq_run (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) :
    polygonState ZeroForce.inertialAt TimeSubdivision.pointAdd a h s n = BoundedIteration.run a h s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change mechanicalCell ZeroForce.inertialAt TimeSubdivision.pointAdd a h
      (polygonState ZeroForce.inertialAt TimeSubdivision.pointAdd a h s n) =
      FiniteEstimates.cell a h (BoundedIteration.run a h s n)
    rw [ih]
    rfl

/-- This edition's own Laws' Corollary I/equal-triangle chain supplies the
finite fan law used in the curve comparison. -/
theorem canonical_fan_law (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (T : Fraction) (s : TimeSubdivision.Point × TimeSubdivision.Point) (j : Nat) :
    Fraction.equiv (PolygonFanArea.fan (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) s k).1)
      (HarmonicDyadic.blocks j)) (Fraction.mul T (CentralSchedule.momentum s)) := by
  have hI : Principia1687.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : Principia1687.Laws.AdditiveImpulse TimeSubdivision.pointAdd :=
    fun _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have ht (k : Nat) := polygon_triangle_equal ZeroForce.inertialAt TimeSubdivision.pointAdd hI hII
    a ha (HarmonicDyadic.duration T j) s k
  simp only [polygonVertex,canonical_polygon_eq_run] at ht
  apply Fraction.equiv_trans (PolygonFanArea.sum_congr _ _ ht (HarmonicDyadic.blocks j))
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant _ _)
  exact Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))
    (Fraction.mul_equiv_right _ (HarmonicDyadic.blocks_duration T j))

/-- Conditional local swept-sector law for one independently supplied
rational-time state curve. MotionSampling.Conditions states the force
comparison, quadratic local mechanical remainder, finite bounds and short
window separately from existence. The chart describes the full curve image and its own
samples. Both force-polygon agreement and slope-mesh exhaustion are derived.

This zero-modern coordinate reconstruction uses this edition's finite laws
and Lemmas III/I. The assigned rational sector area and partial geometric
area convention remain explicit. It does not certify unrestricted curves,
non-rational sectors, winding, or De Motu's different exhaustion argument. -/
theorem sampled_radial_sector_area (area : RadialSector.DifferenceAreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u)
    (A : Fraction) (hA : area.HasArea (MotionSampling.sweptSector u T) A) :
    Fraction.equiv A (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half := by
  let K := (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half
  let F := fun j => PolygonFanArea.fan
    (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1) (HarmonicDyadic.blocks j)
  let Q := fun j => PolygonFanArea.fan (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j)
  let chord := fun j => RadialSector.chordArea g (parts j)
  have hmesh := MotionSampling.sampled_radial_mesh a C T L B P V u d g l r parts chart
  have hAradial := area.congr_set _ _ A (MotionSampling.charted_sector g l r T parts u chart) hA
  have hgeom := (radial_sector_approximation area g l r A parts chart.monotone chart.positive hAradial hmesh).2.1
  have hfan := MotionSampling.sampled_fan_comparison a C T L B P V u d
  have hfinite (j : Nat) : Fraction.equiv
      (SectorFan.areaSum (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1)
        (HarmonicDyadic.blocks j)) K :=
    Fraction.equiv_trans (MotionSampling.areaSum_half_fan _ _)
      (RationalIntervals.half_equiv (canonical_fan_law a ha T _ j))
  have hchord (j : Nat) : Fraction.le (HarmonicTimeComparison.durationDifference K (chord j)).abs
      (HarmonicTimeComparison.durationDifference (F j) (Q j)).abs :=
    Fraction.le_equiv_left (Fraction.abs_equiv (HarmonicTimeComparison.difference_congr
      (Fraction.equiv_symm (hfinite j)) (Fraction.equiv_symm (MotionSampling.sampled_chord_area g l r T parts u chart j))))
      (MotionSampling.areaSum_error_le_fan_error _ _ _)
  let D := (HarmonicTimeComparison.durationDifference K A).abs
  have hbound (j : Nat) : Fraction.le D (Fraction.add
      (HarmonicTimeComparison.durationDifference (F j) (Q j)).abs
      (HarmonicTimeComparison.durationDifference A (chord j)).abs) :=
    Fraction.magnitudes.le_trans (MotionSampling.difference_triangle K (chord j) A)
      (Fraction.add_le_add (hchord j)
        (Fraction.le_of_equiv (HarmonicTimeRealization.durationDifference_abs_symm (chord j) A)))
  have hsmall := MotionSampling.vanishing_add _ _ hfan hgeom
  have hDsmall : Exhaustion.VanishingDifference Fraction.magnitudes (fun _ => D) := by
    intro eps heps
    obtain ⟨N,hN⟩ := hsmall eps heps
    exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (hbound j) (hN j hj)⟩
  have hzero := Principia1687.LemmaI.ultimate_difference_zero (fun _ => D) D
    (Fraction.abs_num_nonnegative _) hDsmall (fun _ _ hd => ⟨0,fun _ _ => hd⟩)
  exact Fraction.equiv_symm (MotionSampling.equiv_of_abs_difference_zero K A hzero)

/-- Areas swept over two admissible windows `[0,T₁]` and `[0,T₂]` from the
same initial state of one given curve compare as their elapsed times. This is
the proportionality conclusion for windows sharing their initial time, with
the local regularity/chart/area scope of sampled_radial_sector_area retained. -/
theorem sampled_radial_sector_comparison (area : RadialSector.DifferenceAreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (C T₁ T₂ L B P V : Fraction) (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d₁ : MotionSampling.Conditions a C T₁ L B P V u)
    (d₂ : MotionSampling.Conditions a C T₂ L B P V u)
    (g₁ g₂ : Fraction → Fraction) (l₁ r₁ l₂ r₂ : Fraction)
    (parts₁ : Nat → MonotoneRectangles.Partition l₁ r₁)
    (parts₂ : Nat → MonotoneRectangles.Partition l₂ r₂)
    (chart₁ : MotionSampling.RadialChart g₁ l₁ r₁ T₁ parts₁ u)
    (chart₂ : MotionSampling.RadialChart g₂ l₂ r₂ T₂ parts₂ u)
    (A₁ A₂ : Fraction) (hA₁ : area.HasArea (MotionSampling.sweptSector u T₁) A₁)
    (hA₂ : area.HasArea (MotionSampling.sweptSector u T₂) A₂) :
    Fraction.equiv (Fraction.mul A₁ T₂) (Fraction.mul A₂ T₁) := by
  have h₁ := sampled_radial_sector_area area a ha C T₁ L B P V u d₁ g₁ l₁ r₁ parts₁ chart₁ A₁ hA₁
  have h₂ := sampled_radial_sector_area area a ha C T₂ L B P V u d₂ g₂ l₂ r₂ parts₂ chart₂ A₂ hA₂
  apply Fraction.equiv_trans (Fraction.mul_equiv_right T₂ h₁)
  apply Fraction.equiv_trans (b := Fraction.mul
    (Fraction.mul T₂ (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half T₁)
  · simp only [Fraction.equiv,Fraction.mul,Fraction.half]
    ac_nf
  · exact Fraction.equiv_symm (Fraction.mul_equiv_right T₁ h₂)


/-- This witness's actual canonical mechanical polygon and the sample-chord
polygon have derived edge bounds and a shrinking cover of their matched
finite locus. This coordinate intermediary supplies no full-curve agreement,
assigned union area or between-region B. Its quantitative statement is an
editorial derivation from the explicit motion premises. -/
theorem mechanical_sampled_chord_control (a : CentralSchedule.Field) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u) :
    (∀ j k, k < HarmonicDyadic.blocks j → ∀ theta, ConvexCover.UnitInterval theta →
      Fraction.le (FiniteEstimates.pointDistance
        (ConvexCover.lerp theta
          (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
            (u (Fraction.ofInt 0)) k)
          (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
            (u (Fraction.ofInt 0)) (k+1)))
        (ConvexCover.lerp theta (MotionSampling.samples u T j k).1
          (MotionSampling.samples u T j (k+1)).1)) (MotionSampling.stateBudget C T j)) ∧
    (∀ j x, ConvexCover.MatchedRegion
      (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)))
      (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j) x →
      ConvexCover.SquareCover (fun k => (MotionSampling.samples u T j k).1)
        (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes (MotionSampling.chordCoverBudget C T V) := by
  refine ⟨?_,?_,MotionSampling.chord_cover_budgets_vanish C T V
    d.remainder_nonnegative d.time_nonnegative d.velocity_nonnegative⟩
  · intro j k hk theta htheta
    simp only [polygonVertex,canonical_polygon_eq_run]
    exact MotionSampling.sampled_chord_edge_bound a C T L B P V u d j k hk theta htheta
  · intro j x
    have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)) = fun k =>
        (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
      funext k
      exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
    rw [hp]
    exact MotionSampling.sampled_chord_cover a C T L B P V u d j x

/-- The independent-parameter finite edge strip has the same cover budget.
Source: this editorial coordinate consequence of the motion premises and this
witness's own canonical polygon identity. Sector-difference inclusion is not
assumed or concluded. -/
theorem mechanical_filled_chord_control (a : CentralSchedule.Field) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u) :
    (∀ j x, ConvexCover.FilledRegion
      (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)))
      (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j) x →
      ConvexCover.SquareCover (fun k => (MotionSampling.samples u T j k).1)
        (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes (MotionSampling.chordCoverBudget C T V) := by
  refine ⟨?_,MotionSampling.chord_cover_budgets_vanish C T V
    d.remainder_nonnegative d.time_nonnegative d.velocity_nonnegative⟩
  intro j x
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp]
  exact MotionSampling.sampled_filled_cover a C T L B P V u d j x

/-- The motion estimates and positive chart derive the finite polygons'
half-plane premise eventually. This witness's own mechanical triangle chain
then assigns the actual sector-union area. Source: this editorial derivation;
the regularity/chart premises are not quotations from Newton. No B or
arbitrary-time polygon agreement is concluded. -/
theorem eventual_mechanical_sector_area (area : SectorFan.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ N, ∀ j, N ≤ j →
      area.HasArea (SectorFan.Region
        (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))) (HarmonicDyadic.blocks j))
        (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half := by
  obtain ⟨N,hN⟩ := MotionSampling.polygon_eventually_positive a C T L B P V u d g l r parts chart
  refine ⟨N,fun j hj => ?_⟩
  have hI : Principia1687.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : Principia1687.Laws.AdditiveImpulse TimeSubdivision.pointAdd :=
    fun _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hp : ∀ k, k ≤ HarmonicDyadic.blocks j →
      0 < (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)) k).1.num := by
    intro k hk
    simp only [polygonVertex,canonical_polygon_eq_run]
    exact hN j hj k hk
  exact area.congr_value _ _ _
    (RationalIntervals.half_equiv (Fraction.mul_equiv_right _
      (HarmonicDyadic.blocks_duration T j)))
    (finite_geometric_sector area ZeroForce.inertialAt TimeSubdivision.pointAdd hI hII a ha
      (HarmonicDyadic.duration T j) d.time_nonnegative (u (Fraction.ofInt 0)) hs
      (HarmonicDyadic.blocks j) hp)


/-- This witness's own finite triangle chain derives the mechanical
orientation. The motion estimates and full positive radial chart then derive
a square/terminal-triangle cover of the mechanical/sample sector-union
symmetric difference eventually. Source: this editorial finite-coordinate
consequence; no difference area, B for the given curve, or arbitrary-time
polygon agreement is assumed or concluded. -/
theorem eventual_mechanical_sector_difference_cover
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ N, ∀ j, N ≤ j →
      let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0))
      let q := fun k => (MotionSampling.samples u T j k).1
      ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧
          ¬ SectorFan.Region q (HarmonicDyadic.blocks j) x) ∨
        (SectorFan.Region q (HarmonicDyadic.blocks j) x ∧
          ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
        ConvexCover.SquareCover q (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x ∨
          SectorFan.Triangle (p (HarmonicDyadic.blocks j)) (q (HarmonicDyadic.blocks j)) x := by
  have hI : Principia1687.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : Principia1687.Laws.AdditiveImpulse TimeSubdivision.pointAdd :=
    fun _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hdet : ∀ j k, k < HarmonicDyadic.blocks j → 0 ≤ (TimeSubdivision.det
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num := by
    intro j k _
    have he := polygon_triangle_equal ZeroForce.inertialAt TimeSubdivision.pointAdd hI hII a ha
      (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k
    have he' := he
    simp only [polygonVertex,canonical_polygon_eq_run] at he'
    exact Fraction.nonnegative_equiv he'
      (Fraction.nonnegative_mul _ _ d.time_nonnegative hs)
  obtain ⟨N,hN⟩ := MotionSampling.eventual_sampled_sector_difference_cover a C T L B P V u d
    g l r parts chart hdet
  refine ⟨N,fun j hj => ?_⟩
  dsimp only
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp]
  exact hN j hj



/-- This witness's own sector-difference inclusion is enclosed by one
finite square union, including its terminal triangle. Its nonnegative
assigned area and vanishing bound are derived under the explicit existing
translation-and-cut area convention. Source: this editorial coordinate
consequence; neither the actual difference's area nor the given curve's B
is constructed, and no new hypothesis is attributed to Newton's text. -/
theorem eventual_mechanical_sector_difference_cover_areas
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (MotionSectorCover.cover a C T B V u j) (A j) ∧
        0 ≤ (A j).num ∧
        Fraction.le (A j) (MotionSectorCover.budget C T B V (u (Fraction.ofInt 0)) j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A ∧
      ∃ N, ∀ j, N ≤ j →
        let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))
        let q := fun k => (MotionSampling.samples u T j k).1
        ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧
            ¬ SectorFan.Region q (HarmonicDyadic.blocks j) x) ∨
          (SectorFan.Region q (HarmonicDyadic.blocks j) x ∧
            ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
          MotionSectorCover.cover a C T B V u j x := by
  obtain ⟨A,hA,hvanish⟩ := MotionSectorCover.cover_areas area a C T B V u
    d.remainder_nonnegative d.time_nonnegative d.force_nonnegative d.velocity_nonnegative
  obtain ⟨N,hN⟩ := eventual_mechanical_sector_difference_cover a ha C T L B P V u d hs
    g l r parts chart
  refine ⟨A,hA,hvanish,N,fun j hj => ?_⟩
  dsimp only
  intro x hx
  rcases hN j hj x hx with h | h
  · exact MotionSectorCover.edge_cover_inside a C T B V u j d.remainder_nonnegative
      d.time_nonnegative d.force_nonnegative x h
  · apply MotionSectorCover.terminal_cover_inside a C T L B P V u d j x
    simpa only [polygonVertex,canonical_polygon_eq_run] using! h


/-- This witness's own mechanical/sample-sector cover is combined with the
derived collar of the full given curve and its chord polygon. The resulting
finite square union has a constructed nonnegative area tending to zero.
Source: this editorial finite-coordinate consequence of the explicitly
stated motion, chart and translation/cut premises. No between-region area
or arbitrary-time polygon/curve agreement is supplied or constructed. -/
theorem eventual_mechanical_curve_between_cover_areas
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (MotionCurveCover.cover a C T B P V u g l r chart.positive j) (A j) ∧
        0 ≤ (A j).num ∧ Fraction.le (A j)
          (MotionCurveCover.budget C T B P V (u (Fraction.ofInt 0)) g l r chart.positive j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A ∧
      ∃ N, ∀ j, N ≤ j →
        let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))
        ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧ ¬ MotionSampling.sweptSector u T x) ∨
          (MotionSampling.sweptSector u T x ∧ ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
          MotionCurveCover.cover a C T B P V u g l r chart.positive j x := by
  obtain ⟨A,hA,hvanish⟩ := MotionCurveCover.cover_areas area a C T B P V u g l r chart.positive
    (MotionCurveCover.chart_terminal_nonnegative g l r T parts u chart)
    d.remainder_nonnegative d.time_nonnegative d.force_nonnegative d.position_nonnegative d.velocity_nonnegative
  obtain ⟨_,_,_,N,hN⟩ := eventual_mechanical_sector_difference_cover_areas area a ha
    C T L B P V u d hs g l r parts chart
  refine ⟨A,hA,hvanish,N,fun j hj => ?_⟩
  dsimp only
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  have hN' := hN j hj
  dsimp only at hN'
  rw [hp] at hN' ⊢
  exact MotionCurveCover.between_cover_of_sector_cover a C T L B P V u d g l r parts chart j hN'

/-- Any separately assigned rational areas of the actual mechanical/curve
sector symmetric differences are nonnegative and vanish. The cover and
exhaustion are conclusions; existence of these between-region areas remains
an explicit premise, separate from existence of the given trajectory. -/
theorem mechanical_between_area_approximation
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u)
    (D : Nat → Fraction) (hD : ∀ j, area.HasArea (MotionCurveCover.between a T u j) (D j)) :
    (∀ j, 0 ≤ (D j).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes D := by
  apply MotionCurveCover.assigned_between_areas_vanish_of_cover area a C T L B P V u d
    g l r parts chart D hD
  obtain ⟨_,_,_,N,hN⟩ := eventual_mechanical_curve_between_cover_areas area a ha
    C T L B P V u d hs g l r parts chart
  refine ⟨N,fun j hj => ?_⟩
  have hN' := hN j hj
  dsimp only at hN'
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp] at hN'
  exact hN'

end Principia1687.PropositionI

/-! 1713. Proposition I finite construction and conditional local rational swept-sector law; unrestricted theorem open. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par50
Anchor URLs: NATP00082.par50 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par50; NATP00082.par51 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51
Proof-step correspondence: The edition's Laws Corollary I is actually used with supplied inertia/additive-change predicates to construct the next vertex and derive equal triangles. Finite composition and radial separation identify ordinary local triangle-union area under explicit area rules. A positive monotone radial sector and its actual chord polygon have derived shrinking area errors and between-region covers, using the edition's Lemmas III/I. A further conditional given-motion reconstruction derives finite sample agreement and mesh exhaustion from explicit quadratic remainders and bounds, then proves the assigned local rational swept-sector area proportional to time. Global/non-rational scope and existence of the between-region area for the mechanical polygons remain open; full Proposition I is not certified.
Historical dependency ledger for this exact witness:
- P1713.Law1 → P1713.P1; passage NATP00082.par51; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status explicit_dependency; confidence high.
- P1713.Composition → P1713.P1; passage NATP00082.par51; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status explicit_dependency; confidence high.
- P1713.L3C4 → P1713.P1; passage NATP00082.par51; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status explicit_dependency; confidence high.
- P1713.L3 → P1713.P1; passage NATP00082.par51 (the quoted Corollary IV curve-limit step); witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status editorial_interpretation; confidence high. The radial triangle exhaustion below applies Lemma III arithmetic in a new coordinate reconstruction, not as an additional explicit Newton citation.
- P1687.P1 → P1713.P1; passage NATP00082.par51; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status editorial_interpretation; confidence high.
-/
/- LATIN BEGIN NATP00082.par50
Areas, quas corpora in gyros acta radiis ad immobile centrum virium ductis describunt, & in planis immobilibus consistere, & esse temporibus proportionales.
LATIN END NATP00082.par50 -/
/- LATIN BEGIN NATP00082.par51
Dividatur tempus in partes æquales, & prima temporis parte describat corpus vi insita rectam AB. Idem secunda temporis parte, si nil impediret, recta pergeret ad c, (per Leg. I.) describens lineam Bc æqualem ipsi AB; adeo ut radiis AS, BS, cS ad centrum actis, confectæ forent æquales areæ ASB, BSc. Verum ubi corpus venit ad B, agat viscentripeta impulsu unico sed magno, effaciatque corpus a recta Bc declinet & pergat in recta BC. Ipsi S BS parallela agatur cC, occurrens BC in C; & completa secunda temporis parte, corpus (per Legum Corol. 1.) reperietur in C, in eodem plano cum triangulo ASB. Junge SC; & triangulum SBC, ob parallelas SB, Cc, æquale erit triangulo SBc, atque adeo etiam triangulo SAB. Simili argumento si vis centripeta successive agat in C, D, E, &c. faciens ut corpus singulis temporis particulis singulas describat rectas CD, DE, EF, &c. jacebunt hæ in eodem plano; & triangulum SCD triangulo SBC & SDE ipsi SCD & SEF ipsi SDE æquale erit. Æqualibus igitur temporibus æquales areæ in plano immoto describuntur: & componendo, sunt arearum summæ quævis SADS, SAFS inter se, ut sunt tempora descriptionum. Augeatur jam numerus & minuatur latitudo triangulorum in infinitum, & eorum ultima perimeter ADF, (per Corollarium quartum Lemmatis tertii) erit linea curva: adeoque vis centripeta, qua corpus de tangente hujus curvæ perpetuo retrahitur, aget indesinenter; areæ vero quævis descriptæ SADS, SAFS temporibus descriptionum semper proportionales, erunt iisdem temporibus in hoc casu proportionales. Q.E.D.
LATIN END NATP00082.par51 -/

namespace Principia1713.PropositionI
open NewtonLimitDynamics.Polygon NewtonLimitDynamics
variable {Point Impulse : Type}

theorem finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

theorem finite_componendo (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

/-! Coordinate realization of the finite historical construction. Inertia
governs each drift and the directed impulse changes its arrival velocity.
The laws are independent mechanical premises; equality of triangle areas
and identification with a local geometric union are proved below. -/

def mechanicalCell
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) : TimeSubdivision.Point × TimeSubdivision.Point :=
  let q := motion s.1 s.2 h
  (q, update s.2 (TimeSubdivision.pointScale h (a q)))

def polygonState
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) : Nat → TimeSubdivision.Point × TimeSubdivision.Point :=
  Nat.rec s (fun _ state => mechanicalCell motion update a h state)

def polygonVertex
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) : TimeSubdivision.Point :=
  (polygonState motion update a h s n).1

open TimeSubdivision in
/-- Newton's AB, Bc, BC step: the edition's Laws Corollary I locates C;
the central direction and the preceding Law I drift give equal triangles.
Neither equal areas nor an areal-product conservation law is a premise. -/
theorem two_triangle_step
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1713.Laws.InertialMotion motion)
    (hII : Principia1713.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (p v : TimeSubdivision.Point) (h : Fraction) :
    Fraction.equiv
      (TimeSubdivision.det (motion p v h)
        (motion (motion p v h) (update v (pointScale h (a (motion p v h)))) h))
      (TimeSubdivision.det p (motion p v h)) := by
  let q := motion p v h
  let j := pointScale h (a q)
  have hcor := Principia1713.Laws.corollary1_from_laws motion update hI hII q v j h
  have hj : Fraction.equiv (TimeSubdivision.det q j) (Fraction.ofInt 0) :=
    Fraction.equiv_trans (det_scale_right h q (a q))
      (Fraction.equiv_trans (Fraction.mul_equiv_left h (ha q)) (Fraction.mul_zero h))
  have hd : Fraction.equiv (TimeSubdivision.det q (Parallelogram.diagonal q (pointScale h v) (pointScale h j)))
      (Fraction.add (Fraction.mul h (TimeSubdivision.det q v)) (Fraction.mul h (TimeSubdivision.det q j))) := by
    simp only [Parallelogram.diagonal,TimeSubdivision.det,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf
    omega
  have hnext : Fraction.equiv
      (TimeSubdivision.det q (motion q (update v j) h))
      (Fraction.mul h (TimeSubdivision.det q v)) :=
    Fraction.equiv_trans (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ hcor)
      (Fraction.equiv_trans hd (Fraction.equiv_trans
        (Fraction.add_equiv_left _ (Fraction.equiv_trans (Fraction.mul_equiv_left h hj)
          (Fraction.mul_zero h))) (Fraction.add_zero _)))
  have hprior : Fraction.equiv (TimeSubdivision.det p q)
      (Fraction.mul h (TimeSubdivision.det p v)) :=
    Fraction.equiv_trans
      (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI p v h))
      (CentralSchedule.det_cell_area p v h)
  have hdrift : Fraction.equiv (TimeSubdivision.det q v) (TimeSubdivision.det p v) :=
    Fraction.equiv_trans (TimeSubdivision.det_congr (hI p v h)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) (CentralSchedule.det_drift p v h)
  exact Fraction.equiv_trans hnext
    (Fraction.equiv_trans (Fraction.mul_equiv_left h hdrift) (Fraction.equiv_symm hprior))

theorem polygon_triangle_equal
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1713.Laws.InertialMotion motion)
    (hII : Principia1713.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) :
    Fraction.equiv
      (TimeSubdivision.det (polygonVertex motion update a h s n) (polygonVertex motion update a h s (n+1)))
      (Fraction.mul h (CentralSchedule.momentum s)) := by
  induction n with
  | zero =>
    exact Fraction.equiv_trans
      (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI s.1 s.2 h))
      (CentralSchedule.det_cell_area s.1 s.2 h)
  | succ n ih =>
    exact Fraction.equiv_trans
      (two_triangle_step motion update hI hII a ha
        (polygonState motion update a h s n).1 (polygonState motion update a h s n).2 h) ih

/-- The historical finite construction now has an actual local sector-union
area, rather than only a multiplicity-counted fan sum. The half-plane and
area convention are explicit geometric premises; this is not the curved
trajectory or the limiting step of Proposition I. -/
theorem finite_geometric_sector
    (area : SectorFan.AreaRules)
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1713.Laws.InertialMotion motion)
    (hII : Principia1713.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (h : Fraction) (hh : 0 ≤ h.num)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hs : 0 ≤ (CentralSchedule.momentum s).num)
    (n : Nat) (hp : ∀ i, i ≤ n → 0 < (polygonVertex motion update a h s i).1.num) :
    area.HasArea (SectorFan.Region (polygonVertex motion update a h s) n)
      (Fraction.mul (BoundedIteration.time h n) (CentralSchedule.momentum s)).half := by
  have htriangle := polygon_triangle_equal motion update hI hII a ha h s
  have hregion := SectorFan.region_area area _ n hp (fun i _ =>
    Fraction.nonnegative_equiv (htriangle i) (Fraction.nonnegative_mul _ _ hh hs))
  apply area.congr_value _ _ _ ?_ hregion
  apply Fraction.equiv_trans
    (PolygonFanArea.sum_congr _ _ (fun i => RationalIntervals.half_equiv (htriangle i)) n)
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant (Fraction.mul h (CentralSchedule.momentum s)).half n)
  simp only [BoundedIteration.time,Fraction.equiv,Fraction.half,Fraction.mul,Fraction.ofInt]
  ac_nf

/-! Local curved-sector exhaustion, in rational coordinates. The given
positive monotone radial graph and its actual chord polygon have derived
geometric enclosures. This applies the edition's Lemma III to radial triangle
areas; it is our reconstruction of an area-limit step, not a quotation of
Newton's rectangle construction. Assigned rational areas and the partial
area convention remain premises. The mesh is in the slope parameter, not yet the equal-time
mechanical polygon's mesh. No force-polygon/curve agreement is assumed or
proved by these geometric declarations. -/
theorem radial_sector_approximation (area : RadialSector.DifferenceAreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 < (g a).num)
    (hA : area.HasArea (RadialSector.sector g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, area.HasArea (RadialSector.chordFigure g (parts m)) (RadialSector.chordArea g (parts m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (RadialSector.chordArea g (parts m))).abs) ∧
    (∀ m x, RadialSector.between g (parts m) x → RadialSector.collar g (parts m) x) ∧
    (∀ m, area.HasArea (RadialSector.collar g (parts m)) (MonotoneRectangles.gap (RadialSector.density g) (parts m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.gap (RadialSector.density g) (parts m)) := by
  have hgap := Principia1713.LemmaIII.unequal_width_gap_vanishes (RadialSector.density g) a b parts
    (RadialSector.density_monotone g a b hg (Int.le_of_lt hbase)) hmesh
  exact ⟨fun m => RadialSector.chord_area area.toSectorAreaRules g (parts m) hg hbase,
    RadialSector.chord_errors_vanish area.toSectorAreaRules g parts hg hbase A hA hgap,
    fun m => RadialSector.between_subset_collar g (parts m) hg hbase,
    fun m => RadialSector.collar_area area g (parts m) hg hbase,hgap⟩

/-- The region between the actual curve and its chord polygon has shrinking
explicit covers above. For any separately assigned rational areas of these
regions, nonnegativity and vanishing are derived, not supplied. -/
theorem radial_between_area_approximation (area : RadialSector.DifferenceAreaRules)
    (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 < (g a).num)
    (B : Nat → Fraction) (hB : ∀ m, area.HasArea (RadialSector.between g (parts m)) (B m))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    (∀ m, 0 ≤ (B m).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes B :=
  RadialSector.between_areas_vanish area g parts hg hbase B hB
    (Principia1713.LemmaIII.unequal_width_gap_vanishes (RadialSector.density g) a b parts
      (RadialSector.density_monotone g a b hg (Int.le_of_lt hbase)) hmesh)

/-- Lemma I excludes a positive terminal chord-area discrepancy after the
actual geometric exhaustion. The supplied terminal comparisons do not
construct a terminal value. -/
theorem radial_ultimate_chord_difference_zero (area : RadialSector.DifferenceAreaRules)
    (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hg : MonotoneRectangles.MonotoneOn g a b) (hbase : 0 < (g a).num)
    (hA : area.HasArea (RadialSector.sector g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m)))
    (D : Fraction) (hD : 0 ≤ D.num)
    (hterminal : Exhaustion.TerminalLower Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (RadialSector.chordArea g (parts m))).abs) D) :
    Fraction.equiv D (Fraction.ofInt 0) :=
  Principia1713.LemmaI.ultimate_difference_zero _ D hD
    (radial_sector_approximation area g a b A parts hg hbase hA hmesh).2.1 hterminal

/-- The coordinate realization of this edition's mechanical polygon is the
same finite drift/kick recurrence used by the comparison estimates. -/
theorem canonical_polygon_eq_run (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) :
    polygonState ZeroForce.inertialAt TimeSubdivision.pointAdd a h s n = BoundedIteration.run a h s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change mechanicalCell ZeroForce.inertialAt TimeSubdivision.pointAdd a h
      (polygonState ZeroForce.inertialAt TimeSubdivision.pointAdd a h s n) =
      FiniteEstimates.cell a h (BoundedIteration.run a h s n)
    rw [ih]
    rfl

/-- This edition's own Laws' Corollary I/equal-triangle chain supplies the
finite fan law used in the curve comparison. -/
theorem canonical_fan_law (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (T : Fraction) (s : TimeSubdivision.Point × TimeSubdivision.Point) (j : Nat) :
    Fraction.equiv (PolygonFanArea.fan (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) s k).1)
      (HarmonicDyadic.blocks j)) (Fraction.mul T (CentralSchedule.momentum s)) := by
  have hI : Principia1713.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : Principia1713.Laws.AdditiveImpulse TimeSubdivision.pointAdd :=
    fun _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have ht (k : Nat) := polygon_triangle_equal ZeroForce.inertialAt TimeSubdivision.pointAdd hI hII
    a ha (HarmonicDyadic.duration T j) s k
  simp only [polygonVertex,canonical_polygon_eq_run] at ht
  apply Fraction.equiv_trans (PolygonFanArea.sum_congr _ _ ht (HarmonicDyadic.blocks j))
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant _ _)
  exact Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))
    (Fraction.mul_equiv_right _ (HarmonicDyadic.blocks_duration T j))

/-- Conditional local swept-sector law for one independently supplied
rational-time state curve. MotionSampling.Conditions states the force
comparison, quadratic local mechanical remainder, finite bounds and short
window separately from existence. The chart describes the full curve image and its own
samples. Both force-polygon agreement and slope-mesh exhaustion are derived.

This zero-modern coordinate reconstruction uses this edition's finite laws
and Lemmas III/I. The assigned rational sector area and partial geometric
area convention remain explicit. It does not certify unrestricted curves,
non-rational sectors, winding, or De Motu's different exhaustion argument. -/
theorem sampled_radial_sector_area (area : RadialSector.DifferenceAreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u)
    (A : Fraction) (hA : area.HasArea (MotionSampling.sweptSector u T) A) :
    Fraction.equiv A (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half := by
  let K := (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half
  let F := fun j => PolygonFanArea.fan
    (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1) (HarmonicDyadic.blocks j)
  let Q := fun j => PolygonFanArea.fan (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j)
  let chord := fun j => RadialSector.chordArea g (parts j)
  have hmesh := MotionSampling.sampled_radial_mesh a C T L B P V u d g l r parts chart
  have hAradial := area.congr_set _ _ A (MotionSampling.charted_sector g l r T parts u chart) hA
  have hgeom := (radial_sector_approximation area g l r A parts chart.monotone chart.positive hAradial hmesh).2.1
  have hfan := MotionSampling.sampled_fan_comparison a C T L B P V u d
  have hfinite (j : Nat) : Fraction.equiv
      (SectorFan.areaSum (fun k => (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1)
        (HarmonicDyadic.blocks j)) K :=
    Fraction.equiv_trans (MotionSampling.areaSum_half_fan _ _)
      (RationalIntervals.half_equiv (canonical_fan_law a ha T _ j))
  have hchord (j : Nat) : Fraction.le (HarmonicTimeComparison.durationDifference K (chord j)).abs
      (HarmonicTimeComparison.durationDifference (F j) (Q j)).abs :=
    Fraction.le_equiv_left (Fraction.abs_equiv (HarmonicTimeComparison.difference_congr
      (Fraction.equiv_symm (hfinite j)) (Fraction.equiv_symm (MotionSampling.sampled_chord_area g l r T parts u chart j))))
      (MotionSampling.areaSum_error_le_fan_error _ _ _)
  let D := (HarmonicTimeComparison.durationDifference K A).abs
  have hbound (j : Nat) : Fraction.le D (Fraction.add
      (HarmonicTimeComparison.durationDifference (F j) (Q j)).abs
      (HarmonicTimeComparison.durationDifference A (chord j)).abs) :=
    Fraction.magnitudes.le_trans (MotionSampling.difference_triangle K (chord j) A)
      (Fraction.add_le_add (hchord j)
        (Fraction.le_of_equiv (HarmonicTimeRealization.durationDifference_abs_symm (chord j) A)))
  have hsmall := MotionSampling.vanishing_add _ _ hfan hgeom
  have hDsmall : Exhaustion.VanishingDifference Fraction.magnitudes (fun _ => D) := by
    intro eps heps
    obtain ⟨N,hN⟩ := hsmall eps heps
    exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (hbound j) (hN j hj)⟩
  have hzero := Principia1713.LemmaI.ultimate_difference_zero (fun _ => D) D
    (Fraction.abs_num_nonnegative _) hDsmall (fun _ _ hd => ⟨0,fun _ _ => hd⟩)
  exact Fraction.equiv_symm (MotionSampling.equiv_of_abs_difference_zero K A hzero)

/-- Areas swept over two admissible windows `[0,T₁]` and `[0,T₂]` from the
same initial state of one given curve compare as their elapsed times. This is
the proportionality conclusion for windows sharing their initial time, with
the local regularity/chart/area scope of sampled_radial_sector_area retained. -/
theorem sampled_radial_sector_comparison (area : RadialSector.DifferenceAreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (C T₁ T₂ L B P V : Fraction) (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d₁ : MotionSampling.Conditions a C T₁ L B P V u)
    (d₂ : MotionSampling.Conditions a C T₂ L B P V u)
    (g₁ g₂ : Fraction → Fraction) (l₁ r₁ l₂ r₂ : Fraction)
    (parts₁ : Nat → MonotoneRectangles.Partition l₁ r₁)
    (parts₂ : Nat → MonotoneRectangles.Partition l₂ r₂)
    (chart₁ : MotionSampling.RadialChart g₁ l₁ r₁ T₁ parts₁ u)
    (chart₂ : MotionSampling.RadialChart g₂ l₂ r₂ T₂ parts₂ u)
    (A₁ A₂ : Fraction) (hA₁ : area.HasArea (MotionSampling.sweptSector u T₁) A₁)
    (hA₂ : area.HasArea (MotionSampling.sweptSector u T₂) A₂) :
    Fraction.equiv (Fraction.mul A₁ T₂) (Fraction.mul A₂ T₁) := by
  have h₁ := sampled_radial_sector_area area a ha C T₁ L B P V u d₁ g₁ l₁ r₁ parts₁ chart₁ A₁ hA₁
  have h₂ := sampled_radial_sector_area area a ha C T₂ L B P V u d₂ g₂ l₂ r₂ parts₂ chart₂ A₂ hA₂
  apply Fraction.equiv_trans (Fraction.mul_equiv_right T₂ h₁)
  apply Fraction.equiv_trans (b := Fraction.mul
    (Fraction.mul T₂ (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half T₁)
  · simp only [Fraction.equiv,Fraction.mul,Fraction.half]
    ac_nf
  · exact Fraction.equiv_symm (Fraction.mul_equiv_right T₁ h₂)


/-- This witness's actual canonical mechanical polygon and the sample-chord
polygon have derived edge bounds and a shrinking cover of their matched
finite locus. This coordinate intermediary supplies no full-curve agreement,
assigned union area or between-region B. Its quantitative statement is an
editorial derivation from the explicit motion premises. -/
theorem mechanical_sampled_chord_control (a : CentralSchedule.Field) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u) :
    (∀ j k, k < HarmonicDyadic.blocks j → ∀ theta, ConvexCover.UnitInterval theta →
      Fraction.le (FiniteEstimates.pointDistance
        (ConvexCover.lerp theta
          (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
            (u (Fraction.ofInt 0)) k)
          (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
            (u (Fraction.ofInt 0)) (k+1)))
        (ConvexCover.lerp theta (MotionSampling.samples u T j k).1
          (MotionSampling.samples u T j (k+1)).1)) (MotionSampling.stateBudget C T j)) ∧
    (∀ j x, ConvexCover.MatchedRegion
      (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)))
      (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j) x →
      ConvexCover.SquareCover (fun k => (MotionSampling.samples u T j k).1)
        (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes (MotionSampling.chordCoverBudget C T V) := by
  refine ⟨?_,?_,MotionSampling.chord_cover_budgets_vanish C T V
    d.remainder_nonnegative d.time_nonnegative d.velocity_nonnegative⟩
  · intro j k hk theta htheta
    simp only [polygonVertex,canonical_polygon_eq_run]
    exact MotionSampling.sampled_chord_edge_bound a C T L B P V u d j k hk theta htheta
  · intro j x
    have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)) = fun k =>
        (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
      funext k
      exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
    rw [hp]
    exact MotionSampling.sampled_chord_cover a C T L B P V u d j x

/-- The independent-parameter finite edge strip has the same cover budget.
Source: this editorial coordinate consequence of the motion premises and this
witness's own canonical polygon identity. Sector-difference inclusion is not
assumed or concluded. -/
theorem mechanical_filled_chord_control (a : CentralSchedule.Field) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u) :
    (∀ j x, ConvexCover.FilledRegion
      (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)))
      (fun k => (MotionSampling.samples u T j k).1) (HarmonicDyadic.blocks j) x →
      ConvexCover.SquareCover (fun k => (MotionSampling.samples u T j k).1)
        (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes (MotionSampling.chordCoverBudget C T V) := by
  refine ⟨?_,MotionSampling.chord_cover_budgets_vanish C T V
    d.remainder_nonnegative d.time_nonnegative d.velocity_nonnegative⟩
  intro j x
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp]
  exact MotionSampling.sampled_filled_cover a C T L B P V u d j x

/-- The motion estimates and positive chart derive the finite polygons'
half-plane premise eventually. This witness's own mechanical triangle chain
then assigns the actual sector-union area. Source: this editorial derivation;
the regularity/chart premises are not quotations from Newton. No B or
arbitrary-time polygon agreement is concluded. -/
theorem eventual_mechanical_sector_area (area : SectorFan.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ N, ∀ j, N ≤ j →
      area.HasArea (SectorFan.Region
        (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))) (HarmonicDyadic.blocks j))
        (Fraction.mul T (CentralSchedule.momentum (u (Fraction.ofInt 0)))).half := by
  obtain ⟨N,hN⟩ := MotionSampling.polygon_eventually_positive a C T L B P V u d g l r parts chart
  refine ⟨N,fun j hj => ?_⟩
  have hI : Principia1713.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : Principia1713.Laws.AdditiveImpulse TimeSubdivision.pointAdd :=
    fun _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hp : ∀ k, k ≤ HarmonicDyadic.blocks j →
      0 < (polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0)) k).1.num := by
    intro k hk
    simp only [polygonVertex,canonical_polygon_eq_run]
    exact hN j hj k hk
  exact area.congr_value _ _ _
    (RationalIntervals.half_equiv (Fraction.mul_equiv_right _
      (HarmonicDyadic.blocks_duration T j)))
    (finite_geometric_sector area ZeroForce.inertialAt TimeSubdivision.pointAdd hI hII a ha
      (HarmonicDyadic.duration T j) d.time_nonnegative (u (Fraction.ofInt 0)) hs
      (HarmonicDyadic.blocks j) hp)


/-- This witness's own finite triangle chain derives the mechanical
orientation. The motion estimates and full positive radial chart then derive
a square/terminal-triangle cover of the mechanical/sample sector-union
symmetric difference eventually. Source: this editorial finite-coordinate
consequence; no difference area, B for the given curve, or arbitrary-time
polygon agreement is assumed or concluded. -/
theorem eventual_mechanical_sector_difference_cover
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ N, ∀ j, N ≤ j →
      let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
        (u (Fraction.ofInt 0))
      let q := fun k => (MotionSampling.samples u T j k).1
      ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧
          ¬ SectorFan.Region q (HarmonicDyadic.blocks j) x) ∨
        (SectorFan.Region q (HarmonicDyadic.blocks j) x ∧
          ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
        ConvexCover.SquareCover q (MotionSampling.chordRadius C T V j) (HarmonicDyadic.blocks j) x ∨
          SectorFan.Triangle (p (HarmonicDyadic.blocks j)) (q (HarmonicDyadic.blocks j)) x := by
  have hI : Principia1713.Laws.InertialMotion ZeroForce.inertialAt :=
    fun _ _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hII : Principia1713.Laws.AdditiveImpulse TimeSubdivision.pointAdd :=
    fun _ _ => ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hdet : ∀ j k, k < HarmonicDyadic.blocks j → 0 ≤ (TimeSubdivision.det
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num := by
    intro j k _
    have he := polygon_triangle_equal ZeroForce.inertialAt TimeSubdivision.pointAdd hI hII a ha
      (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k
    have he' := he
    simp only [polygonVertex,canonical_polygon_eq_run] at he'
    exact Fraction.nonnegative_equiv he'
      (Fraction.nonnegative_mul _ _ d.time_nonnegative hs)
  obtain ⟨N,hN⟩ := MotionSampling.eventual_sampled_sector_difference_cover a C T L B P V u d
    g l r parts chart hdet
  refine ⟨N,fun j hj => ?_⟩
  dsimp only
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp]
  exact hN j hj



/-- This witness's own sector-difference inclusion is enclosed by one
finite square union, including its terminal triangle. Its nonnegative
assigned area and vanishing bound are derived under the explicit existing
translation-and-cut area convention. Source: this editorial coordinate
consequence; neither the actual difference's area nor the given curve's B
is constructed, and no new hypothesis is attributed to Newton's text. -/
theorem eventual_mechanical_sector_difference_cover_areas
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (MotionSectorCover.cover a C T B V u j) (A j) ∧
        0 ≤ (A j).num ∧
        Fraction.le (A j) (MotionSectorCover.budget C T B V (u (Fraction.ofInt 0)) j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A ∧
      ∃ N, ∀ j, N ≤ j →
        let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))
        let q := fun k => (MotionSampling.samples u T j k).1
        ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧
            ¬ SectorFan.Region q (HarmonicDyadic.blocks j) x) ∨
          (SectorFan.Region q (HarmonicDyadic.blocks j) x ∧
            ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
          MotionSectorCover.cover a C T B V u j x := by
  obtain ⟨A,hA,hvanish⟩ := MotionSectorCover.cover_areas area a C T B V u
    d.remainder_nonnegative d.time_nonnegative d.force_nonnegative d.velocity_nonnegative
  obtain ⟨N,hN⟩ := eventual_mechanical_sector_difference_cover a ha C T L B P V u d hs
    g l r parts chart
  refine ⟨A,hA,hvanish,N,fun j hj => ?_⟩
  dsimp only
  intro x hx
  rcases hN j hj x hx with h | h
  · exact MotionSectorCover.edge_cover_inside a C T B V u j d.remainder_nonnegative
      d.time_nonnegative d.force_nonnegative x h
  · apply MotionSectorCover.terminal_cover_inside a C T L B P V u d j x
    simpa only [polygonVertex,canonical_polygon_eq_run] using! h


/-- This witness's own mechanical/sample-sector cover is combined with the
derived collar of the full given curve and its chord polygon. The resulting
finite square union has a constructed nonnegative area tending to zero.
Source: this editorial finite-coordinate consequence of the explicitly
stated motion, chart and translation/cut premises. No between-region area
or arbitrary-time polygon/curve agreement is supplied or constructed. -/
theorem eventual_mechanical_curve_between_cover_areas
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (MotionCurveCover.cover a C T B P V u g l r chart.positive j) (A j) ∧
        0 ≤ (A j).num ∧ Fraction.le (A j)
          (MotionCurveCover.budget C T B P V (u (Fraction.ofInt 0)) g l r chart.positive j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A ∧
      ∃ N, ∀ j, N ≤ j →
        let p := polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
          (u (Fraction.ofInt 0))
        ∀ x, ((SectorFan.Region p (HarmonicDyadic.blocks j) x ∧ ¬ MotionSampling.sweptSector u T x) ∨
          (MotionSampling.sweptSector u T x ∧ ¬ SectorFan.Region p (HarmonicDyadic.blocks j) x)) →
          MotionCurveCover.cover a C T B P V u g l r chart.positive j x := by
  obtain ⟨A,hA,hvanish⟩ := MotionCurveCover.cover_areas area a C T B P V u g l r chart.positive
    (MotionCurveCover.chart_terminal_nonnegative g l r T parts u chart)
    d.remainder_nonnegative d.time_nonnegative d.force_nonnegative d.position_nonnegative d.velocity_nonnegative
  obtain ⟨_,_,_,N,hN⟩ := eventual_mechanical_sector_difference_cover_areas area a ha
    C T L B P V u d hs g l r parts chart
  refine ⟨A,hA,hvanish,N,fun j hj => ?_⟩
  dsimp only
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  have hN' := hN j hj
  dsimp only at hN'
  rw [hp] at hN' ⊢
  exact MotionCurveCover.between_cover_of_sector_cover a C T L B P V u d g l r parts chart j hN'

/-- Any separately assigned rational areas of the actual mechanical/curve
sector symmetric differences are nonnegative and vanish. The cover and
exhaustion are conclusions; existence of these between-region areas remains
an explicit premise, separate from existence of the given trajectory. -/
theorem mechanical_between_area_approximation
    (area : TriangleContent.AreaRules)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (C T L B P V : Fraction)
    (u : Fraction → TimeSubdivision.Point × TimeSubdivision.Point)
    (d : MotionSampling.Conditions a C T L B P V u)
    (hs : 0 ≤ (CentralSchedule.momentum (u (Fraction.ofInt 0))).num)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r)
    (chart : MotionSampling.RadialChart g l r T parts u)
    (D : Nat → Fraction) (hD : ∀ j, area.HasArea (MotionCurveCover.between a T u j) (D j)) :
    (∀ j, 0 ≤ (D j).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes D := by
  apply MotionCurveCover.assigned_between_areas_vanish_of_cover area a C T L B P V u d
    g l r parts chart D hD
  obtain ⟨_,_,_,N,hN⟩ := eventual_mechanical_curve_between_cover_areas area a ha
    C T L B P V u d hs g l r parts chart
  refine ⟨N,fun j hj => ?_⟩
  have hN' := hN j hj
  dsimp only at hN'
  have hp : polygonVertex ZeroForce.inertialAt TimeSubdivision.pointAdd a (HarmonicDyadic.duration T j)
      (u (Fraction.ofInt 0)) = fun k =>
      (BoundedIteration.run a (HarmonicDyadic.duration T j) (u (Fraction.ofInt 0)) k).1 := by
    funext k
    exact congrArg Prod.fst (canonical_polygon_eq_run a _ _ k)
  rw [hp] at hN'
  exact hN'

end Principia1713.PropositionI

/-
===============================================================================
===============================================================================
===============================================================================
===============================================================================
===============================================================================
ANACHRONICAL PROOFS
-/

/-! NATP00089 conditional reconstructions (Latin in the primary witness section above). -/
namespace DeMotu1684.AreaLaw
open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.PathDefect

-- Modern dependency score: 2/7 (M=2, H=5; transitive project theorems/axioms).
theorem natp00089_polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry
-- Modern dependency score: 235/461 (M=235, H=226; transitive project theorems/axioms).
theorem natp00089_constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t
-- Modern dependency score: 243/471 (M=243, H=228; transitive project theorems/axioms).
theorem natp00089_constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁
-- Modern dependency score: 129/311 (M=129, H=182; transitive project theorems/axioms).
theorem natp00089_constructed_boundary_limit (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : TimeSubdivision.Point × TimeSubdivision.Point)
    (hE : 0<E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    CurveTrace.BoundaryLimit (fun m => CurveTrace.ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (CurveTrace.ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

end DeMotu1684.AreaLaw

/-! NATP00090 conditional reconstructions (Latin in the primary witness section above). -/
namespace DeMotu1684.AreaLaw
open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.PathDefect

-- Modern dependency score: 2/7 (M=2, H=5; transitive project theorems/axioms).
theorem natp00090_polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry
-- Modern dependency score: 235/461 (M=235, H=226; transitive project theorems/axioms).
theorem natp00090_constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t
-- Modern dependency score: 243/471 (M=243, H=228; transitive project theorems/axioms).
theorem natp00090_constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁
-- Modern dependency score: 129/311 (M=129, H=182; transitive project theorems/axioms).
theorem natp00090_constructed_boundary_limit (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : TimeSubdivision.Point × TimeSubdivision.Point)
    (hE : 0<E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    CurveTrace.BoundaryLimit (fun m => CurveTrace.ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (CurveTrace.ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

end DeMotu1684.AreaLaw

/-! Principia1687.PropositionI conditional reconstructions (Latin in the primary witness section above). -/
namespace Principia1687.PropositionI
open NewtonLimitDynamics.Polygon NewtonLimitDynamics NewtonLimitDynamics.Polygon.PathDefect

/-- Modern conditional reconstruction for an independently supplied state curve.
`Consistency` gives rational samples and local residual control, not a fan law
or polygon agreement. The conclusions are all-interval fan proportionality
and vanishing nonnegative outer content between paths; ordinary geometric
sector-union identification remains open. -/
-- Modern dependency score: 241/470 (M=241, H=229; transitive project theorems/axioms).
theorem supplied_trajectory_fan_and_path_content
    (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime.BinaryTime T d.time_nonnegative → CauchyValues.Value)
    (c : GivenTrajectoryArea.Consistency o E0 T tau L B s hE d u) :
    SweptArea.Proportional T d.time_nonnegative (fun t => PositionValues.asPosition (u t))
      (CentralSchedule.momentum s) ∧
    ∃ covers : ∀ m, SquareOuterContent.Cover
        (MatchedRegion.Region T d.time_nonnegative
          (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m)
          (fun t => PositionValues.asPosition (u t)) m),
      ∀ eps : Fraction, 0 < eps.num → ∃ N, ∀ m, N ≤ m →
        CauchyValues.Within (SquareContentValues.contentValue _ (covers m)).val
          (CauchyValues.embed (BinaryTime.scalarState (Fraction.ofInt 0))) eps :=
  ⟨GivenTrajectoryArea.proportional_swept_area o E0 T tau L B s hE d u c,
    GivenTrajectoryArea.between_path_content_tends_zero o E0 T tau L B s hE d u c⟩

-- Modern dependency score: 2/7 (M=2, H=5; transitive project theorems/axioms).
theorem polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry

-- Modern dependency score: 235/461 (M=235, H=226; transitive project theorems/axioms).
theorem constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t

-- Modern dependency score: 243/471 (M=243, H=228; transitive project theorems/axioms).
theorem constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁

end Principia1687.PropositionI

/-! Principia1713.PropositionI conditional reconstructions (Latin in the primary witness section above). -/
namespace Principia1713.PropositionI
open NewtonLimitDynamics.Polygon NewtonLimitDynamics NewtonLimitDynamics.Polygon.PathDefect

/-- The same modern supplied-motion fan and path-content reconstruction, kept
separate for the 1713 witness. Its historical limiting step remains open. -/
-- Modern dependency score: 241/470 (M=241, H=229; transitive project theorems/axioms).
theorem supplied_trajectory_fan_and_path_content
    (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime.BinaryTime T d.time_nonnegative → CauchyValues.Value)
    (c : GivenTrajectoryArea.Consistency o E0 T tau L B s hE d u) :
    SweptArea.Proportional T d.time_nonnegative (fun t => PositionValues.asPosition (u t))
      (CentralSchedule.momentum s) ∧
    ∃ covers : ∀ m, SquareOuterContent.Cover
        (MatchedRegion.Region T d.time_nonnegative
          (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m)
          (fun t => PositionValues.asPosition (u t)) m),
      ∀ eps : Fraction, 0 < eps.num → ∃ N, ∀ m, N ≤ m →
        CauchyValues.Within (SquareContentValues.contentValue _ (covers m)).val
          (CauchyValues.embed (BinaryTime.scalarState (Fraction.ofInt 0))) eps :=
  ⟨GivenTrajectoryArea.proportional_swept_area o E0 T tau L B s hE d u c,
    GivenTrajectoryArea.between_path_content_tends_zero o E0 T tau L B s hE d u c⟩

-- Modern dependency score: 2/7 (M=2, H=5; transitive project theorems/axioms).
theorem polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry

-- Modern dependency score: 235/461 (M=235, H=226; transitive project theorems/axioms).
theorem constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t

-- Modern dependency score: 243/471 (M=243, H=228; transitive project theorems/axioms).
theorem constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁

end Principia1713.PropositionI
