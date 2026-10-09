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

theorem cell_norm_bound_at (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hg : Fraction.le (pointNorm (a (cell a h s).1))
      (Fraction.add (Fraction.mul L (pointNorm (cell a h s).1)) E)) :
    Fraction.le (norm tau (cell a h s))
      (Fraction.add (Fraction.mul (amplification tau h L ht) (norm tau s))
        (Fraction.mul (Fraction.mul tau h.abs) E)) := by
  have hp := cell_position_growth a h s
  have ha := Fraction.magnitudes.le_trans hg
    (Fraction.add_le_add_right (Fraction.mul_le_mul_nonnegative_left hp L hL) E)
  have hv := cell_velocity_growth a h _ s ha
  have hb := Fraction.add_le_add hp
    (Fraction.mul_le_mul_nonnegative_left hv tau (Int.le_of_lt ht))
  have hc := component_amplification tau (pointNorm s.1) (pointNorm s.2) h.abs L E
    ht (pointNorm_nonnegative _) (pointNorm_nonnegative _)
    (Fraction.abs_num_nonnegative h) hL
  simpa only [norm,TimeCalibration.amplification,
    Fraction.abs_eq_of_nonnegative h.abs (Fraction.abs_num_nonnegative h)] using!
    (Fraction.magnitudes.le_trans hb hc)


theorem cell_norm_bound (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hg : Growth a L E) :
    Fraction.le (norm tau (cell a h s))
      (Fraction.add (Fraction.mul (amplification tau h L ht) (norm tau s))
        (Fraction.mul (Fraction.mul tau h.abs) E)) :=
  cell_norm_bound_at tau ht a h L E s hL (hg _)

theorem run_norm_budget_at (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) :
    (n : Nat) →
    (hg : ∀ k, k<n → Fraction.le (pointNorm (a (BoundedIteration.run a h s (k+1)).1))
      (Fraction.add (Fraction.mul L (pointNorm (BoundedIteration.run a h s (k+1)).1)) E)) →
    Fraction.le (norm tau (BoundedIteration.run a h s n))
      (Fraction.add (Fraction.mul (fpower (amplification tau h L ht) n) (norm tau s))
        (FiniteRecurrence.sourceBudget (amplification tau h L ht)
          (Fraction.mul (Fraction.mul tau h.abs) E) n))
  | 0, _ => by
      apply Fraction.le_of_equiv
      simp only [BoundedIteration.run,fpower,FiniteRecurrence.sourceBudget,
        Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.add_zero]
  | n+1, hg => by
      have hc := cell_norm_bound_at tau ht a h L E (BoundedIteration.run a h s n) hL (hg n (by omega))
      have hi := Fraction.add_le_add_right
        (Fraction.mul_le_mul_nonnegative_left
          (run_norm_budget_at tau ht a h L E s hL n (fun k hk => hg k (by omega)))
          (amplification tau h L ht) (amplification_nonnegative tau h L ht hL))
        (Fraction.mul (Fraction.mul tau h.abs) E)
      apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans hc hi)
      simp only [FiniteRecurrence.sourceBudget,fpower,Fraction.equiv,Fraction.add,
        Fraction.mul,Int.add_mul,Int.mul_add]
      ac_nf


theorem run_norm_budget (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hg : Growth a L E) :
    (n : Nat) → Fraction.le (norm tau (BoundedIteration.run a h s n))
      (Fraction.add (Fraction.mul (fpower (amplification tau h L ht) n) (norm tau s))
        (FiniteRecurrence.sourceBudget (amplification tau h L ht)
          (Fraction.mul (Fraction.mul tau h.abs) E) n)):=
  fun n => run_norm_budget_at tau ht a h L E s hL n (fun _ _ => hg _)

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

/-- An outer ball large enough for the finite drift-and-kick budget. -/
def driftCap (tau T E : Fraction) (s : Point × Point) (ht : 0 < tau.num) : Fraction :=
  let M := cap tau T E s
  Fraction.add M (Fraction.mul T (Fraction.mul M (inverse tau ht)))

/-- The calibrated window closes the ball budget before any force sample.
Only arithmetic and initial-state magnitudes enter this inequality. -/
theorem driftCap_budget (tau T L E : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) (hT : 0 ≤ T.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hw : Fraction.le (Fraction.mul T (rate tau L ht)) ⟨1,2,by decide⟩) :
    Fraction.le
      (Fraction.add (pointNorm s.1)
        (Fraction.mul T (Fraction.add (pointNorm s.2)
          (Fraction.mul T (Fraction.add (Fraction.mul L (driftCap tau T E s ht)) E)))))
      (driftCap tau T E s ht) := by
  let x := Fraction.mul T (inverse tau ht)
  let y := Fraction.mul (Fraction.mul T tau) L
  have hx0 : 0 ≤ x.num := Fraction.nonnegative_mul _ _ hT (Int.le_of_lt tau.den_pos)
  have hy0 : 0 ≤ y.num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ hT (Int.le_of_lt ht)) hL
  have hsum : Fraction.le (Fraction.add x y) ⟨1,2,by decide⟩ := by
    apply Fraction.le_equiv_left (b := Fraction.mul T (rate tau L ht)) _ hw
    simp only [x,y,rate,Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
    ac_nf
  have hx := Fraction.magnitudes.le_trans (Fraction.le_add_nonnegative x y hy0) hsum
  have hy := Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right (Fraction.le_add_nonnegative y x hx0) (Fraction.add_comm y x)) hsum
  have hxy := Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative hx y hy0)
    (Fraction.mul_le_mul_nonnegative_left hy ⟨1,2,by decide⟩ (by decide))
  have hquad : Fraction.le (Fraction.mul (Fraction.mul T T) L) ⟨1,2,by decide⟩ := by
    apply Fraction.le_equiv_left (b := Fraction.mul x y)
    · simp only [x,y,inverse,Fraction.equiv,Fraction.mul]
      ac_nf
    · exact Fraction.magnitudes.le_trans hxy
        (show Fraction.le (Fraction.mul ⟨1,2,by decide⟩ ⟨1,2,by decide⟩) ⟨1,2,by decide⟩ from by
          change (1:Int)*2 ≤ 1*4
          decide)
  let R := driftCap tau T E s ht
  let F := Fraction.add (pointNorm s.1)
    (Fraction.add (Fraction.mul T (pointNorm s.2)) (Fraction.mul (Fraction.mul T T) E))
  let extra := Fraction.add (Fraction.mul tau (pointNorm s.2))
    (Fraction.add (Fraction.mul (Fraction.mul T (pointNorm s.1)) (inverse tau ht))
      (Fraction.mul (Fraction.mul tau T) E))
  have hextra : 0 ≤ extra.num := Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) (pointNorm_nonnegative _))
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _
        (Fraction.nonnegative_mul _ _ hT (pointNorm_nonnegative _))
        (Int.le_of_lt tau.den_pos))
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) hT) hE))
  have hM := cap_nonnegative tau T E s (Int.le_of_lt ht) hT hE
  have hR : 0 ≤ R.num := Fraction.nonnegative_add _ _ hM
    (Fraction.nonnegative_mul _ _ hT (Fraction.nonnegative_mul _ _ hM (Int.le_of_lt tau.den_pos)))
  have hF : Fraction.le F R.half := by
    apply Fraction.le_equiv_right (Fraction.le_add_nonnegative F extra hextra)
    simp only [F,extra,R,driftCap,cap,norm,inverse,Fraction.equiv,Fraction.half,
      Fraction.add,Fraction.mul,Fraction.ofInt,Int.add_mul,Int.mul_add]
    simp only [show (2:Int)=1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  have hQ : Fraction.le (Fraction.mul (Fraction.mul (Fraction.mul T T) L) R) R.half := by
    apply Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative hquad R hR)
    simp only [Fraction.equiv,Fraction.mul,Fraction.half]
    ac_nf
  apply Fraction.le_equiv_left (b := Fraction.add F (Fraction.mul (Fraction.mul (Fraction.mul T T) L) R))
  · simp only [F,R,Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
    ac_nf
  · exact Fraction.le_equiv_right (Fraction.add_le_add hF hQ) (Fraction.half_add_self R)

/-- Uniform actual-state bound on a calibrated window, for every finite mesh. -/
theorem run_norm_le_cap_at (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h T L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (n : Nat)
    (hg : ∀ k, k<n → Fraction.le (pointNorm (a (BoundedIteration.run a h s (k+1)).1))
      (Fraction.add (Fraction.mul L (pointNorm (BoundedIteration.run a h s (k+1)).1)) E)) (he : Fraction.le (Fraction.mul (Fraction.ofInt (n : Int)) h.abs) T)
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
  apply Fraction.magnitudes.le_trans (run_norm_budget_at tau ht a h L E s hL n hg)
  apply Fraction.magnitudes.le_trans hb
  apply Fraction.le_equiv_right (Fraction.add_le_add_left hsource
    (Fraction.mul (Fraction.ofInt 2) (norm tau s)))
  exact Fraction.equiv_symm (Fraction.mul_add _ _ _)


theorem run_norm_le_cap (tau : Fraction) (ht : 0 < tau.num)
    (a : Point → Point) (h T L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hg : Growth a L E)
    (n : Nat) (he : Fraction.le (Fraction.mul (Fraction.ofInt (n : Int)) h.abs) T)
    (hw : Fraction.le (Fraction.mul T (rate tau L ht)) ⟨1,2,by decide⟩) :
    Fraction.le (norm tau (BoundedIteration.run a h s n)) (cap tau T E s) :=
  run_norm_le_cap_at tau ht a h T L E s hL hE n (fun _ _ => hg _) he hw

end NewtonLimitDynamics.Polygon.CalibratedGrowth
