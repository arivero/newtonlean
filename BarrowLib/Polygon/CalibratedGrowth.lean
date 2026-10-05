import BarrowLib.Polygon.TimeCalibration

/-! Finite calibrated bounds from linear growth of an arbitrary rational map.
No arrival bound or confinement premise is supplied. The recurrence uses the
existing finite amplification and source-budget proofs, rather than an ODE or
an integral inequality. -/

namespace NewtonLimitDynamics.Polygon.CalibratedGrowth
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates
open TimeCalibration HarmonicAccumulation

def Growth (a : Point → Point) (L E : Fraction) : Prop :=
  ∀ p, Fraction.le (pointNorm (a p)) (Fraction.add (Fraction.mul L (pointNorm p)) E)

theorem cell_norm_bound (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hg : Growth a L E) :
    Fraction.le (norm tau (cell a h s))
      (Fraction.add (Fraction.mul (amplification tau h L ht) (norm tau s))
        (Fraction.mul (Fraction.mul tau h.abs) E)) := by
  have hp := cell_position_growth a h s
  have ha := Fraction.magnitudes.le_trans (hg (cell a h s).1)
    (Fraction.add_le_add_right (Fraction.mul_le_mul_nonnegative_left hp L hL) E)
  have hv := cell_velocity_growth a h _ s ha
  have hb := Fraction.add_le_add hp
    (Fraction.mul_le_mul_nonnegative_left hv tau (Int.le_of_lt ht))
  have hc := component_amplification tau (pointNorm s.1) (pointNorm s.2) h.abs L E
    ht (pointNorm_nonnegative _) (pointNorm_nonnegative _)
    (Fraction.abs_num_nonnegative h) hL
  simpa only [norm,TimeCalibration.amplification,
    Fraction.abs_eq_of_nonnegative h.abs (Fraction.abs_num_nonnegative h)] using
    (Fraction.magnitudes.le_trans hb hc)

theorem run_norm_budget (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hg : Growth a L E) :
    (n : Nat) → Fraction.le (norm tau (BoundedIteration.run a h s n))
      (Fraction.add (Fraction.mul (fpower (amplification tau h L ht) n) (norm tau s))
        (FiniteRecurrence.sourceBudget (amplification tau h L ht)
          (Fraction.mul (Fraction.mul tau h.abs) E) n))
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [BoundedIteration.run,fpower,FiniteRecurrence.sourceBudget,
        Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.add_zero]
  | n+1 => by
      have hc := cell_norm_bound tau ht a h L E (BoundedIteration.run a h s n) hL hg
      have hi := Fraction.add_le_add_right
        (Fraction.mul_le_mul_nonnegative_left
          (run_norm_budget tau ht a h L E s hL hg n)
          (amplification tau h L ht) (amplification_nonnegative tau h L ht hL))
        (Fraction.mul (Fraction.mul tau h.abs) E)
      apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans hc hi)
      simp only [FiniteRecurrence.sourceBudget,fpower,Fraction.equiv,Fraction.add,
        Fraction.mul,Int.add_mul,Int.mul_add]
      ac_nf

def cap (tau T E : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul (Fraction.ofInt 2)
    (Fraction.add (norm tau s) (Fraction.mul (Fraction.mul tau T) E))

/-- The derived length cap is invariant under a positive time-unit change. -/
theorem cap_rescale (c tau T E : Fraction) (s : Point × Point) (hc : 0 < c.num) :
    Fraction.equiv
      (cap (Fraction.mul c tau) (Fraction.mul c T) (rescaleConstant c E hc)
        (rescaleState c hc s)) (cap tau T E s) := by
  apply Fraction.mul_equiv (Fraction.equiv_refl _)
  apply Fraction.add_equiv (norm_rescale c tau s hc)
  simp only [rescaleConstant,inverse,Fraction.equiv,Fraction.mul]
  ac_nf

theorem cap_nonnegative (tau T E : Fraction) (s : Point × Point)
    (ht : 0 ≤ tau.num) (hT : 0 ≤ T.num) (hE : 0 ≤ E.num) :
    0 ≤ (cap tau T E s).num :=
  Fraction.nonnegative_mul _ _ (by decide)
    (Fraction.nonnegative_add _ _ (norm_nonnegative tau s ht)
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ ht hT) hE))

/-- Uniform actual-state bound on a calibrated window, for every finite mesh. -/
theorem run_norm_le_cap (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h T L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hg : Growth a L E)
    (n : Nat) (he : Fraction.le (Fraction.mul (Fraction.ofInt (n : Int)) h.abs) T)
    (hw : Fraction.le (Fraction.mul T (rate tau L ht)) ⟨1,2,by decide⟩) :
    Fraction.le (norm tau (BoundedIteration.run a h s n)) (cap tau T E s) := by
  have hp := amplification_power_le_two tau h L ht hL n
    (window_of_elapsed tau h T L ht hL n he hw)
  have hK := amplification_nonnegative tau h L ht hL
  have hC : 0 ≤ (Fraction.mul (Fraction.mul tau h.abs) E).num :=
    Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) (Fraction.abs_num_nonnegative h)) hE
  have hs := FiniteRecurrence.sourceBudget_two_count _ _ n hK hC
    (one_le_amplification tau h L ht hL) hp
  have hb := Fraction.add_le_add
    (Fraction.mul_le_mul_nonnegative hp (norm tau s) (norm_nonnegative _ _ (Int.le_of_lt ht))) hs
  have heq : Fraction.equiv
      (Fraction.mul (Fraction.ofInt (2*(n:Int))) (Fraction.mul (Fraction.mul tau h.abs) E))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (Fraction.mul tau (Fraction.mul (Fraction.ofInt (n:Int)) h.abs)) E)) := by
    simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.mul_one,Int.one_mul]
    ac_nf
  have hsource := Fraction.le_equiv_left heq
    (Fraction.mul_le_mul_nonnegative_left
      (Fraction.mul_le_mul_nonnegative
        (Fraction.mul_le_mul_nonnegative_left he tau (Int.le_of_lt ht)) E hE)
      (Fraction.ofInt 2) (by decide))
  apply Fraction.magnitudes.le_trans (run_norm_budget tau ht a h L E s hL hg n)
  apply Fraction.magnitudes.le_trans hb
  apply Fraction.le_equiv_right (Fraction.add_le_add_left hsource
    (Fraction.mul (Fraction.ofInt 2) (norm tau s)))
  exact Fraction.equiv_symm (Fraction.mul_add _ _ _)

end NewtonLimitDynamics.Polygon.CalibratedGrowth
