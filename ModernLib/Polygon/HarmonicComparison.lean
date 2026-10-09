import BarrowLib.Polygon.StateDistance
import BarrowLib.Polygon.PointBounds
import BarrowLib.Polygon.FiniteEstimates
import ModernLib.Polygon.HarmonicStability

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

def kappa (w h : Fraction) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) h.abs)
    (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs w.abs))

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem zero_le_product (a b : Fraction) (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    Fraction.le (Fraction.ofInt 0) (Fraction.mul a b) := by
  unfold Fraction.le Fraction.ofInt Fraction.mul
  dsimp
  simpa using Int.mul_nonneg ha hb

-- Modern dependency score: 1/11 (M=1, H=10; transitive project theorems/axioms).
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

-- Modern dependency score: 1/11 (M=1, H=10; transitive project theorems/axioms).
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

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem cell_eq_kick_drift (w h : Fraction) (s : Point × Point) :
    cell (linearField w) h s = kick w h (drift h s) := rfl

-- Modern dependency score: 2/25 (M=2, H=23; transitive project theorems/axioms).
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

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem kick_scale_norm (w h : Fraction) (p : Point) :
    Fraction.equiv (pointNorm (pointScale h (linearField w p)))
      (Fraction.mul (Fraction.mul h.abs w.abs) (pointNorm p)) := by
  simp only [Fraction.equiv, pointNorm, pointScale, linearField, negF,
    Fraction.abs, Fraction.add, Fraction.mul, Int.natAbs_mul,
    Int.natAbs_neg, Int.natCast_mul]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

-- Modern dependency score: 3/25 (M=3, H=22; transitive project theorems/axioms).
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
-- Modern dependency score: 7/33 (M=7, H=26; transitive project theorems/axioms).
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
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
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
-- Modern dependency score: 0/20 (M=0, H=20; transitive project theorems/axioms).
theorem linearField_comparison_contract (w : Fraction) :
    FiniteEstimates.comparisonContract (linearField w) (linearField w)
      w.abs (Fraction.ofInt 0) := by
  intro p q
  have hs := FiniteEstimates.difference_scale (negF w) p q
  have he := Fraction.equiv_trans hs
    (Fraction.mul_equiv (Fraction.abs_neg w) (Fraction.equiv_refl _))
  exact Fraction.le_of_equiv (Fraction.equiv_trans he
    (Fraction.equiv_symm (Fraction.add_zero _)))

-- Modern dependency score: 1/47 (M=1, H=46; transitive project theorems/axioms).
theorem cell_perturbation (w h : Fraction) (s t : Point × Point) :
    Fraction.le
      (stateNorm (stateSub (cell (linearField w) h s) (cell (linearField w) h t)))
      (Fraction.mul (kappa w h) (stateNorm (stateSub s t))) := by
  have hg := FiniteEstimates.cell_amplification (linearField w) (linearField w)
    h w.abs (Fraction.ofInt 0) s t (Fraction.abs_num_nonnegative w)
    (linearField_comparison_contract w)
  apply Fraction.le_equiv_right hg
  exact Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _)
    (Fraction.mul_zero h.abs)) (Fraction.add_zero _)

private def one : Fraction := ⟨1, 1, by decide⟩
private def zero : Fraction := ⟨0, 1, by decide⟩
private def half : Fraction := ⟨1, 2, by decide⟩
private def sample : Point × Point := ((one, zero), (zero, one))

/-- Zero duration leaves the represented state unchanged in rational value. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem zero_step (w : Fraction) (s : Point × Point) :
    stateEquiv (cell (linearField w) zero s) s := by
  constructor <;> constructor <;>
    simp only [zero, stateSub, pointEquiv, pointSub, pointNeg, cell, linearField,
      negF, pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
      Int.zero_mul, Int.mul_zero, Int.add_zero] <;>
    ac_nf <;> omega

-- Modern dependency score: 1/11 (M=1, H=10; transitive project theorems/axioms).
theorem zero_step_norm (w : Fraction) (s : Point × Point) :
    Fraction.equiv (stateNorm (cell (linearField w) zero s)) (stateNorm s) :=
  stateNorm_equiv (zero_step w s)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem zero_kappa (w : Fraction) : Fraction.equiv (kappa w zero) one := by
  simp only [kappa, zero, one, Fraction.equiv, Fraction.abs, Fraction.ofInt,
    Fraction.add, Fraction.mul]
  dsimp
  simp only [Int.zero_mul, Int.mul_zero, Int.add_zero, Int.mul_one, Int.one_mul]

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_kappa : Fraction.equiv (kappa one half) ⟨9, 4, by decide⟩ := by decide
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_initial_norm : Fraction.equiv (stateNorm sample) (Fraction.ofInt 2) := by decide
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_cell_norm :
    Fraction.equiv (stateNorm (cell (linearField one) half sample)) ⟨11, 4, by decide⟩ := by decide
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_cell_bound :
    Fraction.le (stateNorm (cell (linearField one) half sample))
      (Fraction.mul (kappa one half) (stateNorm sample)) := by
  unfold Fraction.le
  decide

end NewtonLimitDynamics.Polygon.HarmonicComparison
