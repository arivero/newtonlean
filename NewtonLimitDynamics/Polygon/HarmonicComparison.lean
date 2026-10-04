import NewtonLimitDynamics.Polygon.PointBounds
import NewtonLimitDynamics.Polygon.HarmonicStability

/-!
Finite perturbation comparisons for the actual harmonic end-kick cell. The L1
state magnitude is a chosen coordinate diagnostic and requires a unit
calibration before interpreting position and velocity together physically.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicComparison

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open PointBounds

def stateSub (s t : Point × Point) : Point × Point :=
  (pointSub s.1 t.1, pointSub s.2 t.2)

def kappa (w h : Fraction) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) h.abs)
    (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs w.abs))

private theorem zero_le_product (a b : Fraction) (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    Fraction.le (Fraction.ofInt 0) (Fraction.mul a b) := by
  unfold Fraction.le Fraction.ofInt Fraction.mul
  dsimp
  simpa using Int.mul_nonneg ha hb

private theorem one_plus_bound_right (a b c : Fraction)
    (ha : 0 ≤ a.num) (hc : 0 ≤ c.num) :
    Fraction.le (Fraction.add (Fraction.add a b) (Fraction.mul c b))
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) c) (Fraction.add a b)) := by
  let lhs := Fraction.add (Fraction.add a b) (Fraction.mul c b)
  have h := Fraction.add_le_add_left (zero_le_product c a hc ha) lhs
  have h' : Fraction.le lhs (Fraction.add lhs (Fraction.mul c a)) :=
    Fraction.le_equiv_left (Fraction.equiv_symm (Fraction.add_zero lhs)) h
  apply Fraction.le_equiv_right h'
  simp only [lhs, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
  ac_nf

private theorem one_plus_bound_left (a b c : Fraction)
    (hb : 0 ≤ b.num) (hc : 0 ≤ c.num) :
    Fraction.le (Fraction.add (Fraction.add a b) (Fraction.mul c a))
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) c) (Fraction.add a b)) := by
  let lhs := Fraction.add (Fraction.add a b) (Fraction.mul c a)
  have h := Fraction.add_le_add_left (zero_le_product c b hc hb) lhs
  have h' : Fraction.le lhs (Fraction.add lhs (Fraction.mul c b)) :=
    Fraction.le_equiv_left (Fraction.equiv_symm (Fraction.add_zero lhs)) h
  apply Fraction.le_equiv_right h'
  simp only [lhs, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
  ac_nf

def drift (h : Fraction) (s : Point × Point) : Point × Point :=
  (pointAdd s.1 (pointScale h s.2), s.2)

def kick (w h : Fraction) (s : Point × Point) : Point × Point :=
  (s.1, pointAdd s.2 (pointScale h (linearField w s.1)))

theorem cell_eq_kick_drift (w h : Fraction) (s : Point × Point) :
    cell (linearField w) h s = kick w h (drift h s) := rfl

theorem drift_bound (h : Fraction) (s : Point × Point) :
    Fraction.le (stateNorm (drift h s))
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) h.abs) (stateNorm s)) := by
  have h₁ := Fraction.add_le_add_right (pointNorm_add_le s.1 (pointScale h s.2))
    (pointNorm s.2)
  have h₂ : Fraction.equiv
      (Fraction.add (Fraction.add (pointNorm s.1) (pointNorm (pointScale h s.2)))
        (pointNorm s.2))
      (Fraction.add (Fraction.add (pointNorm s.1) (pointNorm s.2))
        (Fraction.mul h.abs (pointNorm s.2))) := by
    have hs := pointNorm_scale h s.2
    have hh := Fraction.add_equiv (Fraction.equiv_refl (pointNorm s.1)) hs
    have hhh := Fraction.add_equiv hh (Fraction.equiv_refl (pointNorm s.2))
    exact Fraction.equiv_trans hhh (by
      simp only [Fraction.equiv, Fraction.add, Fraction.mul]
      simp only [Int.add_mul, Int.mul_add]
      ac_nf)
  have h₃ := Fraction.le_equiv_right h₁ h₂
  exact Fraction.magnitudes.le_trans h₃
    (one_plus_bound_right (pointNorm s.1) (pointNorm s.2) h.abs
      (pointNorm_nonnegative _) (Fraction.abs_num_nonnegative _))

private theorem kick_scale_norm (w h : Fraction) (p : Point) :
    Fraction.equiv (pointNorm (pointScale h (linearField w p)))
      (Fraction.mul (Fraction.mul h.abs w.abs) (pointNorm p)) := by
  simp only [Fraction.equiv, pointNorm, pointScale, linearField, negF,
    Fraction.abs, Fraction.add, Fraction.mul, Int.natAbs_mul,
    Int.natAbs_neg, Int.ofNat_mul]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

theorem kick_bound (w h : Fraction) (s : Point × Point) :
    Fraction.le (stateNorm (kick w h s))
      (Fraction.mul
        (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs w.abs))
        (stateNorm s)) := by
  have h₁ := Fraction.add_le_add_left
    (pointNorm_add_le s.2 (pointScale h (linearField w s.1))) (pointNorm s.1)
  have h₂ : Fraction.equiv
      (Fraction.add (pointNorm s.1)
        (Fraction.add (pointNorm s.2)
          (pointNorm (pointScale h (linearField w s.1)))))
      (Fraction.add (Fraction.add (pointNorm s.1) (pointNorm s.2))
        (Fraction.mul (Fraction.mul h.abs w.abs) (pointNorm s.1))) := by
    have hf := kick_scale_norm w h s.1
    have hh := Fraction.add_equiv (Fraction.equiv_refl (pointNorm s.2)) hf
    have hhh := Fraction.add_equiv (Fraction.equiv_refl (pointNorm s.1)) hh
    exact Fraction.equiv_trans hhh (by
      simp only [Fraction.equiv, Fraction.add, Fraction.mul]
      simp only [Int.add_mul, Int.mul_add]
      ac_nf)
  have h₃ := Fraction.le_equiv_right h₁ h₂
  exact Fraction.magnitudes.le_trans h₃
    (one_plus_bound_left (pointNorm s.1) (pointNorm s.2)
      (Fraction.mul h.abs w.abs) (pointNorm_nonnegative _)
      (Int.mul_nonneg (Fraction.abs_num_nonnegative _) (Fraction.abs_num_nonnegative _)))

/-- One actual harmonic end-kick cell amplifies the coordinate L1 state
magnitude by at most `(1+|h|)(1+|h||w|)`, including signed and zero data. -/
theorem cell_bound (w h : Fraction) (s : Point × Point) :
    Fraction.le (stateNorm (cell (linearField w) h s))
      (Fraction.mul (kappa w h) (stateNorm s)) := by
  rw [cell_eq_kick_drift]
  have hk := kick_bound w h (drift h s)
  have hd := drift_bound h s
  have hc : 0 ≤ (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs w.abs)).num := by
    have hp := Int.mul_pos h.abs.den_pos w.abs.den_pos
    have hn := Int.mul_nonneg (Fraction.abs_num_nonnegative h)
      (Fraction.abs_num_nonnegative w)
    unfold Fraction.add Fraction.ofInt Fraction.mul
    dsimp
    omega
  have hm := Fraction.mul_le_mul_nonnegative_left hd
    (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs w.abs)) hc
  have hchain := Fraction.magnitudes.le_trans hk hm
  apply Fraction.le_equiv_right hchain
  simp only [kappa, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
  ac_nf

/-- Subtracting the outputs of two actual cells equals applying the same
linear harmonic cell to their input difference, as rational values. -/
theorem cell_difference (w h : Fraction) (s t : Point × Point) :
    stateEquiv (stateSub (cell (linearField w) h s) (cell (linearField w) h t))
      (cell (linearField w) h (stateSub s t)) := by
  constructor <;> constructor <;>
    simp only [zero, stateSub, pointEquiv, pointSub, pointNeg, cell, linearField,
      negF, pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- A one-step perturbation estimate for two actual cells under the same
linear field and duration. The input difference is a represented state. -/
theorem cell_perturbation (w h : Fraction) (s t : Point × Point) :
    Fraction.le
      (stateNorm (stateSub (cell (linearField w) h s) (cell (linearField w) h t)))
      (Fraction.mul (kappa w h) (stateNorm (stateSub s t))) :=
  Fraction.le_equiv_left (stateNorm_equiv (cell_difference w h s t))
    (cell_bound w h (stateSub s t))

private def one : Fraction := ⟨1, 1, by decide⟩
private def zero : Fraction := ⟨0, 1, by decide⟩
private def half : Fraction := ⟨1, 2, by decide⟩
private def sample : Point × Point := ((one, zero), (zero, one))

/-- Zero duration leaves the represented state unchanged in rational value. -/
theorem zero_step (w : Fraction) (s : Point × Point) :
    stateEquiv (cell (linearField w) zero s) s := by
  constructor <;> constructor <;>
    simp only [zero, stateSub, pointEquiv, pointSub, pointNeg, cell, linearField,
      negF, pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
      Int.zero_mul, Int.mul_zero, Int.add_zero] <;>
    ac_nf <;> omega

theorem zero_step_norm (w : Fraction) (s : Point × Point) :
    Fraction.equiv (stateNorm (cell (linearField w) zero s)) (stateNorm s) :=
  stateNorm_equiv (zero_step w s)

theorem zero_kappa (w : Fraction) : Fraction.equiv (kappa w zero) one := by
  simp only [kappa, zero, one, Fraction.equiv, Fraction.abs, Fraction.ofInt,
    Fraction.add, Fraction.mul]
  dsimp
  simp only [Int.zero_mul, Int.mul_zero, Int.add_zero, Int.mul_one, Int.one_mul]

theorem sample_kappa : Fraction.equiv (kappa one half) ⟨9, 4, by decide⟩ := by decide
theorem sample_initial_norm : Fraction.equiv (stateNorm sample) (Fraction.ofInt 2) := by decide
theorem sample_cell_norm :
    Fraction.equiv (stateNorm (cell (linearField one) half sample)) ⟨11, 4, by decide⟩ := by decide
theorem sample_cell_bound :
    Fraction.le (stateNorm (cell (linearField one) half sample))
      (Fraction.mul (kappa one half) (stateNorm sample)) := by
  unfold Fraction.le
  decide

end NewtonLimitDynamics.Polygon.HarmonicComparison
