import BarrowLib.Polygon.IntegerSchedule
import NewtonLimitDynamics.Polygon.HarmonicTimeRealization

/-! Finite unequal subdivision identities for the actual harmonic end-kick cell. -/

namespace NewtonLimitDynamics.Polygon.HarmonicIntegerSubdivision

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicDyadic
open HarmonicComparison
open PointBounds
open HarmonicAccumulation
open IntegerSchedule

def integerFine (w h : Fraction) (s : Point × Point) (k : Nat) : Point × Point :=
  schedule (linearField w) (List.replicate k h) s

def integerCoarse (w h : Fraction) (s : Point × Point) (k : Nat) : Point × Point :=
  cell (linearField w) (integerDuration h k) s

/-- The position defect caused by replacing one `(a+b)` cell with an `a`
cell followed by a `b` cell. The sampled force is at the actual first arrival. -/
theorem split_position_identity (w a b : Fraction) (s : Point × Point) :
    pointEquiv
      (stateSub (cell (linearField w) b (cell (linearField w) a s))
        (cell (linearField w) (Fraction.add a b) s)).1
      (pointScale (Fraction.mul a b)
        (linearField w (cell (linearField w) a s).1)) := by
  constructor <;>
    simp only [stateSub, cell, linearField, negF, pointEquiv, pointSub,
      pointNeg, pointAdd, pointScale, Fraction.equiv, Fraction.add,
      Fraction.mul, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- The velocity defect contains a sampling shift of the initial velocity
and the second kick applied to the position defect. -/
theorem split_velocity_identity (w a b : Fraction) (s : Point × Point) :
    pointEquiv
      (stateSub (cell (linearField w) b (cell (linearField w) a s))
        (cell (linearField w) (Fraction.add a b) s)).2
      (pointAdd
        (pointScale (negF (Fraction.mul a b)) (linearField w s.2))
        (pointScale (Fraction.mul b (Fraction.mul a b))
          (linearField w (linearField w (cell (linearField w) a s).1)))) := by
  constructor <;>
    simp only [stateSub, cell, linearField, negF, pointEquiv, pointSub,
      pointNeg, pointAdd, pointScale, Fraction.equiv, Fraction.add,
      Fraction.mul, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- A local state bound with every force sample still at its actual point.
For `a=i*h` and `b=h`, all three coefficients contain two step factors. -/
theorem split_state_sample_bound (w a b : Fraction) (s : Point × Point) :
    Fraction.le
      (stateNorm (stateSub
        (cell (linearField w) b (cell (linearField w) a s))
        (cell (linearField w) (Fraction.add a b) s)))
      (Fraction.add
        (Fraction.mul (Fraction.mul a b).abs
          (pointNorm (linearField w (cell (linearField w) a s).1)))
        (Fraction.add
          (Fraction.mul (Fraction.mul a b).abs
            (pointNorm (linearField w s.2)))
          (Fraction.mul (Fraction.mul b (Fraction.mul a b)).abs
            (pointNorm
              (linearField w
                (linearField w (cell (linearField w) a s).1)))))) := by
  have hp := pointNorm_equiv (split_position_identity w a b s)
  have hv := pointNorm_equiv (split_velocity_identity w a b s)
  have htri := pointNorm_add_le
    (pointScale (negF (Fraction.mul a b)) (linearField w s.2))
    (pointScale (Fraction.mul b (Fraction.mul a b))
      (linearField w (linearField w (cell (linearField w) a s).1)))
  have hraw := Fraction.add_le_add_left
    (Fraction.le_equiv_left hv htri)
    (pointNorm (stateSub
      (cell (linearField w) b (cell (linearField w) a s))
      (cell (linearField w) (Fraction.add a b) s)).1)
  have hepos := Fraction.equiv_trans hp
    (pointNorm_scale (Fraction.mul a b)
      (linearField w (cell (linearField w) a s).1))
  have hevel₁ := Fraction.equiv_trans
    (pointNorm_scale (negF (Fraction.mul a b)) (linearField w s.2))
    (Fraction.mul_equiv
      (Fraction.abs_neg (Fraction.mul a b)) (Fraction.equiv_refl _))
  have hevel₂ := pointNorm_scale (Fraction.mul b (Fraction.mul a b))
    (linearField w (linearField w (cell (linearField w) a s).1))
  change Fraction.le
    (Fraction.add
      (pointNorm (stateSub
        (cell (linearField w) b (cell (linearField w) a s))
        (cell (linearField w) (Fraction.add a b) s)).1)
      (pointNorm (stateSub
        (cell (linearField w) b (cell (linearField w) a s))
        (cell (linearField w) (Fraction.add a b) s)).2)) _
  exact Fraction.le_equiv_right hraw
    (Fraction.add_equiv hepos (Fraction.add_equiv hevel₁ hevel₂))

theorem linearField_norm (w : Fraction) (p : Point) :
    Fraction.equiv (pointNorm (linearField w p))
      (Fraction.mul w.abs (pointNorm p)) := by
  exact Fraction.equiv_trans (pointNorm_scale (negF w) p)
    (Fraction.mul_equiv (Fraction.abs_neg w) (Fraction.equiv_refl _))

/-- The local defect uses only the initial velocity and the actual first
arrival. Every term contains `a*b`; the last also contains `b`. -/
theorem split_state_harmonic_bound (w a b : Fraction) (s : Point × Point) :
    Fraction.le
      (stateNorm (stateSub
        (cell (linearField w) b (cell (linearField w) a s))
        (cell (linearField w) (Fraction.add a b) s)))
      (Fraction.add
        (Fraction.mul (Fraction.mul a b).abs
          (Fraction.mul w.abs
            (pointNorm (cell (linearField w) a s).1)))
        (Fraction.add
          (Fraction.mul (Fraction.mul a b).abs
            (Fraction.mul w.abs (pointNorm s.2)))
          (Fraction.mul (Fraction.mul b (Fraction.mul a b)).abs
            (Fraction.mul w.abs
              (Fraction.mul w.abs
                (pointNorm (cell (linearField w) a s).1)))))) := by
  have h := split_state_sample_bound w a b s
  have hp := linearField_norm w (cell (linearField w) a s).1
  have hv := linearField_norm w s.2
  have hpp := Fraction.equiv_trans
    (linearField_norm w (linearField w (cell (linearField w) a s).1))
    (Fraction.mul_equiv (Fraction.equiv_refl _ ) hp)
  exact Fraction.le_equiv_right h
    (Fraction.add_equiv
      (Fraction.mul_equiv (Fraction.equiv_refl _) hp)
      (Fraction.add_equiv
        (Fraction.mul_equiv (Fraction.equiv_refl _) hv)
        (Fraction.mul_equiv (Fraction.equiv_refl _) hpp)))

def uniformSplitBudget (w a b M : Fraction) : Fraction :=
  Fraction.add
    (Fraction.mul (Fraction.mul a b).abs (Fraction.mul w.abs M))
    (Fraction.add
      (Fraction.mul (Fraction.mul a b).abs (Fraction.mul w.abs M))
      (Fraction.mul (Fraction.mul a b).abs
        (Fraction.mul w.abs (Fraction.mul w.abs M))))

/-- If the first arrival and initial velocity lie in one rational L1 ball,
the unequal split has a uniform quadratic-step source. -/
theorem split_state_uniform_bound (w a b M : Fraction) (s : Point × Point)
    (hb : Fraction.le b.abs (Fraction.ofInt 1))
    (hP : Fraction.le (pointNorm (cell (linearField w) a s).1) M)
    (hV : Fraction.le (pointNorm s.2) M) :
    Fraction.le
      (stateNorm (stateSub
        (cell (linearField w) b (cell (linearField w) a s))
        (cell (linearField w) (Fraction.add a b) s)))
      (uniformSplitBudget w a b M) := by
  have hp₁ := Fraction.mul_le_mul_nonnegative_left hP w.abs
    (Fraction.abs_num_nonnegative w)
  have hp := Fraction.mul_le_mul_nonnegative_left hp₁
    (Fraction.mul a b).abs (Fraction.abs_num_nonnegative _)
  have hv₁ := Fraction.mul_le_mul_nonnegative_left hV w.abs
    (Fraction.abs_num_nonnegative w)
  have hv := Fraction.mul_le_mul_nonnegative_left hv₁
    (Fraction.mul a b).abs (Fraction.abs_num_nonnegative _)
  have hpp₁ := Fraction.mul_le_mul_nonnegative_left hp₁ w.abs
    (Fraction.abs_num_nonnegative w)
  have hM : 0 ≤ M.num := by
    have hPnum := pointNorm_nonnegative (cell (linearField w) a s).1
    have hden := (pointNorm (cell (linearField w) a s).1).den_pos
    have hMden := M.den_pos
    unfold Fraction.le at hP
    by_cases hn : 0 ≤ M.num
    · exact hn
    have hnegative : M.num * (pointNorm (cell (linearField w) a s).1).den < 0 :=
      Int.mul_neg_of_neg_of_pos (by omega) hden
    have hpositive : 0 ≤
        (pointNorm (cell (linearField w) a s).1).num * M.den :=
      Int.mul_nonneg hPnum (Int.le_of_lt hMden)
    omega
  have hcoef : Fraction.le (Fraction.mul b (Fraction.mul a b)).abs
      (Fraction.mul a b).abs := by
    have hm := Fraction.mul_le_mul_nonnegative hb (Fraction.mul a b).abs
      (Fraction.abs_num_nonnegative _)
    exact Fraction.le_equiv_left
      (Fraction.abs_mul b (Fraction.mul a b))
      (Fraction.le_equiv_right hm (by
        simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
        simp))
  have hcoef₂ := Fraction.mul_le_mul_nonnegative hcoef
    (Fraction.mul w.abs (Fraction.mul w.abs M))
    (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w)
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w)
        hM))
  have hpp := Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative_left hpp₁
      (Fraction.mul b (Fraction.mul a b)).abs
      (Fraction.abs_num_nonnegative _)) hcoef₂
  exact Fraction.magnitudes.le_trans
    (split_state_harmonic_bound w a b s)
    (Fraction.add_le_add hp (Fraction.add_le_add hv hpp))

theorem first_arrival_le_state (w a : Fraction) (s : Point × Point)
    (ha : Fraction.le a.abs (Fraction.ofInt 1)) :
    Fraction.le (pointNorm (cell (linearField w) a s).1) (stateNorm s) := by
  have hp := FiniteEstimates.cell_position_growth (linearField w) a s
  have hm := Fraction.mul_le_mul_nonnegative ha (pointNorm s.2)
    (pointNorm_nonnegative s.2)
  have hunit : Fraction.equiv
      (Fraction.mul (Fraction.ofInt 1) (pointNorm s.2))
      (pointNorm s.2) := by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    simp
  have hv := Fraction.le_equiv_right hm hunit
  have hsum := Fraction.add_le_add_left hv (pointNorm s.1)
  exact Fraction.magnitudes.le_trans hp hsum

/-- An unequal split whose two durations have absolute value at most one
has a defect bounded by its product duration and the initial state ball. -/
theorem split_state_short_bound (w a b : Fraction) (s : Point × Point)
    (ha : Fraction.le a.abs (Fraction.ofInt 1))
    (hb : Fraction.le b.abs (Fraction.ofInt 1)) :
    Fraction.le
      (stateNorm (stateSub
        (cell (linearField w) b (cell (linearField w) a s))
        (cell (linearField w) (Fraction.add a b) s)))
      (uniformSplitBudget w a b (stateNorm s)) :=
  split_state_uniform_bound w a b (stateNorm s) s hb
    (first_arrival_le_state w a s ha) (velocity_le_state s)

def splitFactor (w : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (Fraction.mul w.abs (stateNorm s))
    (Fraction.add (Fraction.mul w.abs (stateNorm s))
      (Fraction.mul w.abs (Fraction.mul w.abs (stateNorm s))))

theorem uniformSplitBudget_factor (w a b : Fraction) (s : Point × Point) :
    Fraction.equiv (uniformSplitBudget w a b (stateNorm s))
      (Fraction.mul (Fraction.mul a b).abs (splitFactor w s)) := by
  simp only [uniformSplitBudget, splitFactor, Fraction.equiv,
    Fraction.add, Fraction.mul]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

theorem splitFactor_nonnegative (w : Fraction) (s : Point × Point) :
    0 ≤ (splitFactor w s).num := by
  unfold splitFactor
  apply Fraction.nonnegative_add
  · exact Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w)
      (stateNorm_nonnegative s)
  · apply Fraction.nonnegative_add
    · exact Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w)
        (stateNorm_nonnegative s)
    · exact Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w)
        (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w)
          (stateNorm_nonnegative s))

theorem integer_duration_product_abs (h : Fraction) (k : Nat)
    (hh : 0 ≤ h.num) :
    Fraction.equiv (Fraction.mul (IntegerSchedule.integerDuration h k) h).abs
      (Fraction.mul (Fraction.ofInt (k : Int)) (Fraction.mul h h)) := by
  have h₁ := Fraction.abs_equiv
    (Fraction.mul_equiv (IntegerSchedule.integerDuration_closed h k)
      (Fraction.equiv_refl h))
  have h₂ := Fraction.abs_mul
    (Fraction.mul (Fraction.ofInt (k : Int)) h) h
  have h₃ := Fraction.mul_equiv
    (Fraction.abs_mul (Fraction.ofInt (k : Int)) h)
    (Fraction.abs_of_nonnegative h hh)
  have h₄ := Fraction.mul_equiv
    (Fraction.mul_equiv
      (Fraction.abs_of_nonnegative (Fraction.ofInt (k : Int)) (Int.ofNat_nonneg k))
      (Fraction.abs_of_nonnegative h hh)) (Fraction.equiv_refl h)
  exact Fraction.equiv_trans h₁
    (Fraction.equiv_trans h₂ (Fraction.equiv_trans h₃
      (Fraction.equiv_trans h₄ (Fraction.mul_assoc _ _ _))))

def kappaCap (w : Fraction) : Fraction :=
  Fraction.mul (Fraction.ofInt 2)
    (Fraction.add (Fraction.ofInt 1) w.abs)

theorem kappaCap_nonnegative (w : Fraction) : 0 ≤ (kappaCap w).num :=
  Fraction.nonnegative_mul _ _ (by decide)
    (Fraction.nonnegative_add _ _ (by decide)
      (Fraction.abs_num_nonnegative w))

theorem kappa_le_cap (w h : Fraction)
    (hh : Fraction.le h.abs (Fraction.ofInt 1)) :
    Fraction.le (kappa w h) (kappaCap w) := by
  have h₂ : Fraction.le
      (Fraction.add (Fraction.ofInt 1) h.abs) (Fraction.ofInt 2) := by
    exact Fraction.le_equiv_right
      (Fraction.add_le_add_left hh (Fraction.ofInt 1)) (by decide)
  have hw₁ := Fraction.mul_le_mul_nonnegative hh w.abs
    (Fraction.abs_num_nonnegative w)
  have hw₂ := Fraction.add_le_add_left hw₁ (Fraction.ofInt 1)
  have hnon : 0 ≤
      (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs w.abs)).num :=
    Fraction.nonnegative_add _ _ (by decide)
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
        (Fraction.abs_num_nonnegative w))
  have hm₁ := Fraction.mul_le_mul_nonnegative h₂
    (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs w.abs)) hnon
  have hm₂ := Fraction.mul_le_mul_nonnegative_left hw₂ (Fraction.ofInt 2)
    (by decide)
  exact Fraction.magnitudes.le_trans hm₁
    (Fraction.le_equiv_right hm₂ (by
      simp only [kappaCap, Fraction.equiv, Fraction.add, Fraction.mul,
        Fraction.ofInt]
      simp only [Int.one_mul, Int.mul_one]))

def integerLocalBudget (w h : Fraction) (s : Point × Point) (k : Nat) : Fraction :=
  Fraction.add
    (Fraction.mul (Fraction.mul (integerDuration h k) h).abs
      (Fraction.mul w.abs (pointNorm (integerCoarse w h s k).1)))
    (Fraction.add
      (Fraction.mul (Fraction.mul (integerDuration h k) h).abs
        (Fraction.mul w.abs (pointNorm s.2)))
      (Fraction.mul (Fraction.mul h (Fraction.mul (integerDuration h k) h)).abs
        (Fraction.mul w.abs
          (Fraction.mul w.abs (pointNorm (integerCoarse w h s k).1)))))

/-- Actual `k`-cell subdivision recurrence. The source is the measured
unequal-cell defect at the coarse first arrival, not a supplied Cauchy bound. -/
theorem integer_error_step (w h : Fraction) (s : Point × Point) (k : Nat) :
    Fraction.le
      (stateNorm (stateSub
        (integerFine w h s (k + 1)) (integerCoarse w h s (k + 1))))
      (Fraction.add
        (Fraction.mul (kappa w h)
          (stateNorm (stateSub
            (integerFine w h s k) (integerCoarse w h s k))))
        (integerLocalBudget w h s k)) := by
  have htri := stateSub_triangle
    (cell (linearField w) h (integerFine w h s k))
    (cell (linearField w) h (integerCoarse w h s k))
    (integerCoarse w h s (k + 1))
  have hp := cell_perturbation w h (integerFine w h s k)
    (integerCoarse w h s k)
  have hl := split_state_harmonic_bound w (integerDuration h k) h s
  have hsum := Fraction.add_le_add hp hl
  have hbound := Fraction.magnitudes.le_trans htri hsum
  simpa only [integerFine, integerCoarse, integerDuration,
    HarmonicBinaryPrefix.schedule_replicate_step, integerLocalBudget] using hbound

theorem integer_error_step_quadratic (w h : Fraction)
    (s : Point × Point) (k : Nat)
    (hh : 0 ≤ h.num)
    (ha : Fraction.le (integerDuration h k).abs (Fraction.ofInt 1))
    (hb : Fraction.le h.abs (Fraction.ofInt 1)) :
    Fraction.le
      (stateNorm (stateSub
        (integerFine w h s (k + 1)) (integerCoarse w h s (k + 1))))
      (Fraction.add
        (Fraction.mul (kappa w h)
          (stateNorm (stateSub
            (integerFine w h s k) (integerCoarse w h s k))))
        (Fraction.mul
          (Fraction.mul (Fraction.ofInt (k : Int)) (Fraction.mul h h))
          (splitFactor w s))) := by
  have htri := stateSub_triangle
    (cell (linearField w) h (integerFine w h s k))
    (cell (linearField w) h (integerCoarse w h s k))
    (integerCoarse w h s (k + 1))
  have hp := cell_perturbation w h (integerFine w h s k)
    (integerCoarse w h s k)
  have hl := split_state_short_bound w (integerDuration h k) h s ha hb
  have he := Fraction.equiv_trans
    (uniformSplitBudget_factor w (integerDuration h k) h s)
    (Fraction.mul_equiv (integer_duration_product_abs h k hh)
      (Fraction.equiv_refl _))
  have hlocal := Fraction.le_equiv_right hl he
  have hsum := Fraction.add_le_add hp hlocal
  have hbound := Fraction.magnitudes.le_trans htri hsum
  simpa only [integerFine, integerCoarse, integerDuration,
    HarmonicBinaryPrefix.schedule_replicate_step] using hbound

def integerErrorBudget (w h : Fraction) (s : Point × Point) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | k + 1 => Fraction.add
      (Fraction.mul (kappa w h) (integerErrorBudget w h s k))
      (integerLocalBudget w h s k)

/-- Every finite integer subdivision is controlled by the recursively
computed actual local sources and one-cell amplification. -/
theorem integer_error_le_budget (w h : Fraction) (s : Point × Point) :
    (k : Nat) → Fraction.le
      (stateNorm (stateSub (integerFine w h s k) (integerCoarse w h s k)))
      (integerErrorBudget w h s k)
  | 0 => by
      have he := zero_step w s
      have he' : Fraction.equiv
          (stateNorm (stateSub (cell (linearField w) (Fraction.ofInt 0) s) s))
          (stateNorm (stateSub s s)) :=
        stateNorm_equiv (stateSub_congr he
        ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
          ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩)
      have hz := Fraction.equiv_trans
        (stateSub_norm_symm s (cell (linearField w) (Fraction.ofInt 0) s))
        (Fraction.equiv_trans he' (stateSub_self_norm_zero s))
      simpa only [integerFine, integerCoarse, integerDuration,
        integerErrorBudget, List.replicate_zero, schedule] using
        Fraction.le_of_equiv hz
  | k + 1 => by
      have hi := integer_error_le_budget w h s k
      have hm := Fraction.mul_le_mul_nonnegative_left hi (kappa w h)
        (kappa_nonnegative w h)
      have hs := Fraction.add_le_add_right hm (integerLocalBudget w h s k)
      exact Fraction.magnitudes.le_trans (integer_error_step w h s k) hs

def quadraticCap (w : Fraction) (s : Point × Point) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | k + 1 => Fraction.add
      (Fraction.mul (kappaCap w) (quadraticCap w s k))
      (Fraction.mul (Fraction.ofInt (k : Int)) (splitFactor w s))

theorem quadraticCap_nonnegative (w : Fraction) (s : Point × Point) :
    (k : Nat) → 0 ≤ (quadraticCap w s k).num
  | 0 => by simp [quadraticCap, Fraction.ofInt]
  | k + 1 => Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _ (kappaCap_nonnegative w)
        (quadraticCap_nonnegative w s k))
      (Fraction.nonnegative_mul _ _ (Int.ofNat_nonneg k)
        (splitFactor_nonnegative w s))

/-- For each fixed integer `k`, the discrepancy between one `k*h` cell
and `k` actual `h` cells is at most `h²` times a coefficient independent
of `h`. The stated short-prefix condition is finite and will be discharged
from the global dyadic window before passing to Cauchy values. -/
theorem integer_error_quadratic (w h : Fraction) (s : Point × Point)
    (hh : 0 ≤ h.num) (hb : Fraction.le h.abs (Fraction.ofInt 1)) :
    (k : Nat) →
      (∀ i, i ≤ k → Fraction.le (integerDuration h i).abs (Fraction.ofInt 1)) →
      Fraction.le
        (stateNorm (stateSub (integerFine w h s k) (integerCoarse w h s k)))
        (Fraction.mul (Fraction.mul h h) (quadraticCap w s k))
  | 0, _ => by
      have h₀ := integer_error_le_budget w h s 0
      apply Fraction.le_equiv_right h₀
      simp only [integerErrorBudget, quadraticCap, Fraction.equiv,
        Fraction.mul, Fraction.ofInt]
      simp
  | k + 1, hshort => by
      have hprev := integer_error_quadratic w h s hh hb k
        (fun i hi => hshort i (by omega))
      have hstep := integer_error_step_quadratic w h s k hh
        (hshort k (by omega)) hb
      have hkappa := kappa_le_cap w h hb
      have h₂ : 0 ≤ (Fraction.mul h h).num :=
        Fraction.nonnegative_mul _ _ hh hh
      have hC : 0 ≤
          (Fraction.mul (Fraction.mul h h) (quadraticCap w s k)).num :=
        Fraction.nonnegative_mul _ _ h₂ (quadraticCap_nonnegative w s k)
      have h₁ := Fraction.mul_le_mul_nonnegative_left hprev (kappa w h)
        (kappa_nonnegative w h)
      have h₂' := Fraction.mul_le_mul_nonnegative hkappa
        (Fraction.mul (Fraction.mul h h) (quadraticCap w s k)) hC
      have h₃ := Fraction.magnitudes.le_trans h₁ h₂'
      have hsum := Fraction.add_le_add_right h₃
        (Fraction.mul
          (Fraction.mul (Fraction.ofInt (k : Int)) (Fraction.mul h h))
          (splitFactor w s))
      have hbound := Fraction.magnitudes.le_trans hstep hsum
      apply Fraction.le_equiv_right hbound
      simp only [quadraticCap, Fraction.equiv, Fraction.mul,
        Fraction.add, Fraction.ofInt]
      simp only [Int.add_mul, Int.mul_add]
      ac_nf

end NewtonLimitDynamics.Polygon.HarmonicIntegerSubdivision
