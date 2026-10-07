import NewtonLimitDynamics

/-! A positive-time given inertial curve has a full radial chart. Its area
exists under the explicit triangle convention, and both printed-edition
proofs identify any assigned swept-sector area. No polygon agreement,
shrinking mesh or area proportionality is supplied. -/
namespace NewtonLimitDynamics.Polygon.HistoricalMotionAreaControls
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates MotionSampling
open HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization MonotoneRectangles RadialSector

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))
private def z := Fraction.ofInt 0
private def o := Fraction.ofInt 1
private def two := Fraction.ofInt 2
private def T : Fraction := ⟨1,4,by decide⟩
private def force : Point → Point := fun _ => (z,z)
private def curve (t : Fraction) : Point × Point := ((o,t),(z,o))
private def g : Fraction → Fraction := fun _ => o
private def timeAt (j k : Nat) : Fraction := if k=0 then z else countTime T j k
private theorem time_equiv (j k : Nat) : Fraction.equiv (timeAt j k) (countTime T j k) := by
  by_cases h : k=0
  · subst k
    simp only [timeAt,if_pos,z,countTime,Fraction.equiv,Fraction.mul,Fraction.ofInt,
      Int.natCast_zero,Int.zero_mul,Int.mul_zero]
  · simp only [timeAt,if_neg h]; exact Fraction.equiv_refl _
private theorem time_next (j k : Nat) :
    Fraction.equiv (timeAt j (k+1)) (Fraction.add (timeAt j k) (duration T j)) := by
  apply Fraction.equiv_trans (time_equiv j (k+1))
  apply Fraction.equiv_trans (b := Fraction.add (countTime T j k) (duration T j))
  · simp only [countTime,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  · exact Fraction.add_equiv_right _ (Fraction.equiv_symm (time_equiv j k))
private theorem curve_congr {s t : Fraction} (h : Fraction.equiv s t) : stateEquiv (curve s) (curve t) :=
  ⟨⟨Fraction.equiv_refl _,h⟩,⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩
private theorem curve_cell (t h : Fraction) :
    stateEquiv (curve (Fraction.add t h)) (cell force h (curve t)) := by
  constructor <;> constructor <;>
    simp only [curve,force,cell,pointAdd,pointScale,z,o,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.zero_add,Int.add_zero] <;> ac_nf
private theorem conditions : Conditions force z T z z two o curve := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,?_,?_,by decide,?_,?_,?_⟩
  · intro p r
    exact Fraction.le_of_equiv (Fraction.equiv_trans (pointDistance_self_zero (force p))
      (Fraction.equiv_symm (Fraction.equiv_trans (Fraction.mul_comm _ _) (Fraction.mul_zero _))))
  · intro j k _
    have he : stateEquiv (curve (timeAt j (k+1))) (cell force (duration T j) (curve (timeAt j k))) :=
      ⟨pointEquiv_trans (curve_congr (time_next j k)).1 (curve_cell _ _).1,
        pointEquiv_trans (curve_congr (time_next j k)).2 (curve_cell _ _).2⟩
    have hd : Fraction.equiv (stateDistance (curve (timeAt j (k+1)))
        (cell force (duration T j) (curve (timeAt j k)))) z :=
      Fraction.equiv_trans (Fraction.add_equiv
        (pointDistance_equiv he.1 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
        (pointDistance_equiv he.2 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)) (stateDistance_self_zero _)
    exact Fraction.le_of_equiv (Fraction.equiv_trans hd
      (Fraction.equiv_symm (Fraction.equiv_trans (Fraction.mul_comm _ _) (Fraction.mul_zero _))))
  · intro j k _
    change (0 : Int) ≤ 0
    decide
  · intro j k hk
    have ht : Fraction.le (timeAt j k) T := Fraction.le_equiv_left (time_equiv j k)
      (Fraction.le_equiv_right (BoundedIteration.time_monotone (duration T j) (by change (0 : Int) ≤ 1; decide)
        k (blocks j) (by omega)) (blocks_duration T j))
    have htn : 0 ≤ (timeAt j k).num := Fraction.nonnegative_equiv (time_equiv j k)
      (Fraction.nonnegative_mul _ _ (Int.ofNat_nonneg _) (by change (0 : Int) ≤ 1; decide))
    have he : Fraction.equiv (pointNorm (curve (timeAt j k)).1) (Fraction.add o (timeAt j k)) :=
      Fraction.add_equiv (Fraction.abs_of_nonnegative _ (by change (0 : Int) ≤ 1; decide)) (Fraction.abs_of_nonnegative _ htn)
    exact Fraction.le_equiv_left he (Fraction.magnitudes.le_trans (Fraction.add_le_add_left ht o)
      (by change Fraction.le (Fraction.add o T) two; decide))
  · intro j k _
    change (1 : Int) ≤ 1
    decide
private def parts (j : Nat) : Partition z T where
  count := blocks j
  positive_count := by unfold blocks; exact Nat.pow_pos (by decide)
  nodes := countTime T j
  first := by simp only [countTime,z,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_zero,
    Int.zero_mul,Int.mul_zero]
  last := blocks_duration T j
  ordered := by
    intro i _
    simp only [Fraction.le,countTime,Fraction.mul,Fraction.ofInt,Int.natCast_add,Int.natCast_one,
      Int.mul_one,Int.one_mul,duration,T,Int.add_mul,Int.mul_add]
    have hp : 0 < (2 : Int)^j := Int.pow_pos (by decide)
    omega
private theorem curve_ray (t : Fraction) : pointEquiv (curve t).1 (ray (g t) t) := by
  constructor
  · exact Fraction.equiv_refl _
  · simp only [ray,curve,g,o,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
private theorem chart : RadialChart g z T T parts curve where
  monotone := fun _ _ _ _ _ => Fraction.magnitudes.le_refl _
  positive := by decide
  count := fun _ => rfl
  curve_points := fun t ht0 htT => ⟨t,ht0,htT,curve_ray t⟩
  graph_points := fun t ht0 htT => ⟨t,ht0,htT,curve_ray t⟩
  samples := by
    intro j k _
    exact pointEquiv_trans (curve_congr (time_equiv j k)).1 (curve_ray _)
private theorem central : CentralSchedule.central force := by
  intro p
  simp only [force,TimeSubdivision.det,z,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.zero_mul,Int.mul_zero,Int.neg_zero,Int.add_zero]
private theorem actual_area (area : DifferenceAreaRules) : area.HasArea (sweptSector curve T) T.half := by
  have hc := caps_enclosure g z T o o (by decide) chart.monotone chart.positive
    (by decide) (Fraction.magnitudes.le_refl _) (Fraction.magnitudes.le_refl _)
  have ha := area.triangle (ray o z) (ray o T) (ray_orientation _ _ _ _ (by decide) (by decide) (by decide))
  have hr : area.HasArea (sector g z T) T.half := area.congr_set _ _ _
    (fun x => ⟨hc.1 x,hc.2 x⟩) (area.congr_value _ _ _ (by decide) ha)
  exact area.congr_set _ _ _ (fun x => (charted_sector g z T T parts curve chart x).symm) hr

example : 0 < T.num := by decide
example (area : DifferenceAreaRules) : area.HasArea (sweptSector curve T) T.half := actual_area area
example (area : DifferenceAreaRules) (A : Fraction) (hA : area.HasArea (sweptSector curve T) A) :
    Fraction.equiv A T.half :=
  Fraction.equiv_trans (Principia1687.PropositionI.sampled_radial_sector_area area force central
    z T z z two o curve conditions g z T parts chart A hA) (by decide)
example (area : DifferenceAreaRules) (A : Fraction) (hA : area.HasArea (sweptSector curve T) A) :
    Fraction.equiv A T.half :=
  Fraction.equiv_trans (Principia1713.PropositionI.sampled_radial_sector_area area force central
    z T z z two o curve conditions g z T parts chart A hA) (by decide)

#print axioms Principia1687.PropositionI.sampled_radial_sector_area
#print axioms Principia1713.PropositionI.sampled_radial_sector_area
end NewtonLimitDynamics.Polygon.HistoricalMotionAreaControls
