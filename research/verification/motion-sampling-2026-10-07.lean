import BarrowLib

/-! A constant acceleration and an independently prescribed quadratic curve
exercise nonzero local remainders. This acceleration is deliberately not
central about the origin, so this control does not assert Proposition I. -/
namespace NewtonLimitDynamics.Polygon.MotionSamplingControls
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates MotionSampling
open HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))
private def z := Fraction.ofInt 0
private def o := Fraction.ofInt 1
private def two := Fraction.ofInt 2
private def T : Fraction := ⟨1,4,by decide⟩
private def force : Point → Point := fun _ => (two,z)
private def curve (t : Fraction) : Point × Point :=
  ((Fraction.mul t t,t),(Fraction.mul two t,o))
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
  ⟨⟨Fraction.mul_equiv h h,h⟩,⟨Fraction.mul_equiv_left two h,Fraction.equiv_refl _⟩⟩

private theorem polynomial_residual (t h : Fraction) (hh : 0 ≤ h.num) :
    Fraction.equiv (stateDistance (curve (Fraction.add t h)) (cell force h (curve t))) (Fraction.mul h h) := by
  have he : stateEquiv
      (HarmonicComparison.stateSub (curve (Fraction.add t h)) (cell force h (curve t)))
      ((Fraction.mul h h,z),(z,z)) := by
    constructor <;> constructor <;>
      simp only [HarmonicComparison.stateSub,curve,force,cell,pointSub,pointAdd,pointScale,pointNeg,
        z,o,two,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one,Int.zero_mul,Int.mul_zero] <;>
      ac_nf <;> (try simp only [← Int.mul_assoc]) <;> omega
  apply Fraction.equiv_trans (stateNorm_equiv he)
  apply Fraction.equiv_trans (b := (Fraction.mul h h).abs)
  · simp only [stateNorm,pointNorm,z,Fraction.equiv,Fraction.abs,Fraction.add,Fraction.ofInt,
      Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add,Int.one_mul,Int.mul_one,
      Int.natAbs_zero,Int.natCast_zero]
  · exact Fraction.abs_of_nonnegative _ (Fraction.nonnegative_mul _ _ hh hh)

private theorem times_bounds (j k : Nat) (hk : k ≤ blocks j) :
    0 ≤ (timeAt j k).num ∧ Fraction.le (timeAt j k) T := by
  have ht : Fraction.le (countTime T j k) T :=
    Fraction.le_equiv_right (BoundedIteration.time_monotone (duration T j) (by change (0 : Int) ≤ 1; decide)
      k (blocks j) hk) (blocks_duration T j)
  constructor
  · exact Fraction.nonnegative_equiv (time_equiv j k)
      (Fraction.nonnegative_mul _ _ (Int.ofNat_nonneg _) (by change (0 : Int) ≤ 1; decide))
  · exact Fraction.le_equiv_left (time_equiv j k) ht
private theorem curve_norms (t : Fraction) (ht : 0 ≤ t.num) :
    Fraction.equiv (pointNorm (curve t).1) (Fraction.add (Fraction.mul t t) t) ∧
    Fraction.equiv (pointNorm (curve t).2) (Fraction.add (Fraction.mul two t) o) :=
  ⟨Fraction.add_equiv (Fraction.abs_of_nonnegative _ (Fraction.nonnegative_mul _ _ ht ht))
      (Fraction.abs_of_nonnegative _ ht),
    Fraction.add_equiv (Fraction.abs_of_nonnegative _ (Fraction.nonnegative_mul _ _ (by decide) ht))
      (Fraction.abs_of_nonnegative _ (by change (0 : Int) ≤ 1; decide))⟩

private theorem conditions : Conditions force o T z two o two curve := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,?_,?_,by decide,?_,?_,?_⟩
  · intro p r
    exact Fraction.le_of_equiv (Fraction.equiv_trans (pointDistance_self_zero (force p))
      (Fraction.equiv_symm (Fraction.equiv_trans (Fraction.mul_comm _ _) (Fraction.mul_zero _))))
  · intro j k _
    have hc := curve_congr (time_next j k)
    have he : Fraction.equiv (stateDistance (curve (timeAt j (k+1)))
        (cell force (duration T j) (curve (timeAt j k))))
        (stateDistance (curve (Fraction.add (timeAt j k) (duration T j)))
          (cell force (duration T j) (curve (timeAt j k)))) := Fraction.add_equiv
      (pointDistance_equiv hc.1 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (pointDistance_equiv hc.2 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
    apply Fraction.le_of_equiv (Fraction.equiv_trans he (Fraction.equiv_trans
      (polynomial_residual (timeAt j k) (duration T j) (by change (0 : Int) ≤ 1; decide)) ?_))
    simp only [remainder,o,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
  · intro j k _
    change (2 : Int) ≤ 2
    decide
  · intro j k hk
    have ht := times_bounds j k (by omega)
    have hs := Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative ht.2 (timeAt j k) ht.1)
      (Fraction.mul_le_mul_nonnegative_left ht.2 T (by decide))
    exact Fraction.le_equiv_left (curve_norms _ ht.1).1
      (Fraction.magnitudes.le_trans (Fraction.add_le_add hs ht.2) (by change Fraction.le (Fraction.add (Fraction.mul T T) T) o; decide))
  · intro j k hk
    have ht := times_bounds j k (by omega)
    exact Fraction.le_equiv_left (curve_norms _ ht.1).2
      (Fraction.magnitudes.le_trans (Fraction.add_le_add_right
        (Fraction.mul_le_mul_nonnegative_left ht.2 two (by decide)) o) (by change Fraction.le (Fraction.add (Fraction.mul two T) o) two; decide))

example : ∀ eps, 0 < eps.num → ∃ N, ∀ j, N ≤ j → ∀ k, k ≤ blocks j →
    Fraction.lt (stateDistance (BoundedIteration.run force (duration T j) (curve z) k)
      (samples curve T j k)) eps :=
  sampled_agreement force o T z two o two curve conditions
example : Fraction.equiv (stateBudget o T 0) ⟨1,8,by decide⟩ := by decide
example : ¬ CentralSchedule.central force := by
  intro h
  have he := h (o,o)
  have hn : ¬ Fraction.equiv (TimeSubdivision.det (o,o) (force (o,o))) z := by decide
  exact hn he

#print axioms MotionSampling.sampled_agreement
#print axioms MotionSampling.sampled_fan_comparison
#print axioms MotionSampling.sampled_radial_mesh
end NewtonLimitDynamics.Polygon.MotionSamplingControls
