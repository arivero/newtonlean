import BarrowLib.Polygon.BoundedIteration
import BarrowLib.Polygon.IntegerSchedule
import BarrowLib.Polygon.FiniteRecurrence
import NewtonLimitDynamics.Polygon.HarmonicTimeRealization

/-! Finite unequal subdivision identities for the actual harmonic end-kick cell. -/

namespace NewtonLimitDynamics.Polygon.HarmonicIntegerSubdivision

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicDyadic
open HarmonicBinaryPrefix
open HarmonicComparison
open PointBounds
open HarmonicAccumulation
open HarmonicUniform
open IntegerSchedule
open FiniteRecurrence

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

/-- Lipschitz control of an actual block of `k` end-kick cells. -/
theorem integerFine_perturbation (w h : Fraction)
    (s t : Point × Point) :
    (k : Nat) → Fraction.le
      (stateNorm (stateSub (integerFine w h s k) (integerFine w h t k)))
      (Fraction.mul (fpower (kappa w h) k) (stateNorm (stateSub s t)))
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [integerFine, List.replicate_zero, schedule,
        fpower, Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp
  | k + 1 => by
      have hp := cell_perturbation w h (integerFine w h s k)
        (integerFine w h t k)
      have hi := integerFine_perturbation w h s t k
      have hm := Fraction.mul_le_mul_nonnegative_left hi (kappa w h)
        (kappa_nonnegative w h)
      have hchain := Fraction.magnitudes.le_trans hp hm
      have hfinal := Fraction.le_equiv_right hchain
        (Fraction.equiv_symm (Fraction.mul_assoc
          (kappa w h) (fpower (kappa w h) k)
          (stateNorm (stateSub s t))))
      simpa only [integerFine, HarmonicBinaryPrefix.schedule_replicate_step,
        fpower] using hfinal

def fineBlocks (w h : Fraction) (k : Nat) (s : Point × Point) :
    Nat → Point × Point
  | 0 => s
  | N + 1 => integerFine w h (fineBlocks w h k s N) k

def coarseBlocks (w h : Fraction) (k : Nat) (s : Point × Point) :
    Nat → Point × Point
  | 0 => s
  | N + 1 => integerCoarse w h (coarseBlocks w h k s N) k

theorem block_error_step (w h : Fraction) (k : Nat)
    (s : Point × Point) (N : Nat)
    (hh : 0 ≤ h.num) (hb : Fraction.le h.abs (Fraction.ofInt 1))
    (hshort : ∀ i, i ≤ k →
      Fraction.le (integerDuration h i).abs (Fraction.ofInt 1)) :
    Fraction.le
      (stateNorm (stateSub
        (fineBlocks w h k s (N + 1)) (coarseBlocks w h k s (N + 1))))
      (Fraction.add
        (Fraction.mul (fpower (kappa w h) k)
          (stateNorm (stateSub
            (fineBlocks w h k s N) (coarseBlocks w h k s N))))
        (Fraction.mul (Fraction.mul h h)
          (quadraticCap w (coarseBlocks w h k s N) k))) := by
  let f := fineBlocks w h k s N
  let c := coarseBlocks w h k s N
  have htri := stateSub_triangle
    (integerFine w h f k) (integerFine w h c k)
    (integerCoarse w h c k)
  have hp := integerFine_perturbation w h f c k
  have hl := integer_error_quadratic w h c hh hb k hshort
  have hbound := Fraction.magnitudes.le_trans htri
    (Fraction.add_le_add hp hl)
  simpa only [fineBlocks, coarseBlocks] using hbound

theorem splitFactor_le (w : Fraction) (s t : Point × Point)
    (hst : Fraction.le (stateNorm s) (stateNorm t)) :
    Fraction.le (splitFactor w s) (splitFactor w t) := by
  have h₁ := Fraction.mul_le_mul_nonnegative_left hst w.abs
    (Fraction.abs_num_nonnegative w)
  have h₂ := Fraction.mul_le_mul_nonnegative_left h₁ w.abs
    (Fraction.abs_num_nonnegative w)
  exact Fraction.add_le_add h₁ (Fraction.add_le_add h₁ h₂)

theorem splitFactor_double (w : Fraction) (s t : Point × Point)
    (hst : Fraction.le (stateNorm s)
      (Fraction.mul (Fraction.ofInt 2) (stateNorm t))) :
    Fraction.le (splitFactor w s)
      (Fraction.mul (Fraction.ofInt 2) (splitFactor w t)) := by
  have h₁ := Fraction.mul_le_mul_nonnegative_left hst w.abs
    (Fraction.abs_num_nonnegative w)
  have h₂ := Fraction.mul_le_mul_nonnegative_left h₁ w.abs
    (Fraction.abs_num_nonnegative w)
  have hsum := Fraction.add_le_add h₁ (Fraction.add_le_add h₁ h₂)
  apply Fraction.le_equiv_right hsum
  simp only [splitFactor, Fraction.equiv, Fraction.add, Fraction.mul,
    Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

theorem quadraticCap_double (w : Fraction) (s t : Point × Point)
    (hst : Fraction.le (stateNorm s)
      (Fraction.mul (Fraction.ofInt 2) (stateNorm t))) :
    (k : Nat) → Fraction.le (quadraticCap w s k)
      (Fraction.mul (Fraction.ofInt 2) (quadraticCap w t k))
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [quadraticCap, Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp
  | k + 1 => by
      have hi := quadraticCap_double w s t hst k
      have hs := splitFactor_double w s t hst
      have h₁ := Fraction.mul_le_mul_nonnegative_left hi (kappaCap w)
        (kappaCap_nonnegative w)
      have h₂ := Fraction.mul_le_mul_nonnegative_left hs
        (Fraction.ofInt (k : Int)) (Int.ofNat_nonneg k)
      have hsum := Fraction.add_le_add h₁ h₂
      apply Fraction.le_equiv_right hsum
      simp only [quadraticCap, Fraction.equiv, Fraction.add,
        Fraction.mul, Fraction.ofInt]
      simp only [Int.add_mul, Int.mul_add]
      ac_nf

theorem coarseBlocks_norm_bound (w h : Fraction) (k : Nat)
    (s : Point × Point) :
    (N : Nat) → Fraction.le (stateNorm (coarseBlocks w h k s N))
      (Fraction.mul (fpower (kappa w (integerDuration h k)) N)
        (stateNorm s))
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [coarseBlocks, fpower, Fraction.equiv,
        Fraction.mul, Fraction.ofInt]
      simp
  | N + 1 => by
      have hc := cell_bound w (integerDuration h k)
        (coarseBlocks w h k s N)
      have hi := coarseBlocks_norm_bound w h k s N
      have hm := Fraction.mul_le_mul_nonnegative_left hi
        (kappa w (integerDuration h k))
        (kappa_nonnegative w (integerDuration h k))
      have hbound := Fraction.magnitudes.le_trans hc hm
      apply Fraction.le_equiv_right hbound
      simp only [coarseBlocks, integerCoarse, fpower, Fraction.equiv,
        Fraction.mul]
      ac_nf

theorem coarseBlocks_state_le_two (w h : Fraction) (k : Nat)
    (s : Point × Point) (N : Nat)
    (hpower : Fraction.le
      (fpower (kappa w (integerDuration h k)) N) (Fraction.ofInt 2)) :
    (i : Nat) → i ≤ N → Fraction.le
      (stateNorm (coarseBlocks w h k s i))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) := by
  intro i hi
  let r := kappa w (integerDuration h k)
  have hpref := fpower_prefix_le r (kappa_nonnegative w _) (one_le_kappa w _)
    i N hi
  have hp := Fraction.magnitudes.le_trans hpref hpower
  have hm := Fraction.mul_le_mul_nonnegative hp (stateNorm s)
    (stateNorm_nonnegative s)
  exact Fraction.magnitudes.le_trans (coarseBlocks_norm_bound w h k s i) hm

def blockSource (w h : Fraction) (k : Nat) (s : Point × Point) : Fraction :=
  Fraction.mul (Fraction.mul h h)
    (Fraction.mul (Fraction.ofInt 2) (quadraticCap w s k))

theorem blockSource_nonnegative (w h : Fraction) (k : Nat)
    (s : Point × Point) (hh : 0 ≤ h.num) :
    0 ≤ (blockSource w h k s).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ hh hh)
    (Fraction.nonnegative_mul _ _ (by decide)
      (quadraticCap_nonnegative w s k))

/-- Finite accumulation with a measured coarse-state confinement and an
explicit short-prefix premise. No Cauchy or partition-independence field. -/
theorem block_error_le_budget (w h : Fraction) (k : Nat)
    (s : Point × Point) (N : Nat)
    (hh : 0 ≤ h.num) (hb : Fraction.le h.abs (Fraction.ofInt 1))
    (hshort : ∀ j, j ≤ k →
      Fraction.le (integerDuration h j).abs (Fraction.ofInt 1))
    (hcoarsePower : Fraction.le
      (fpower (kappa w (integerDuration h k)) N) (Fraction.ofInt 2)) :
    (i : Nat) → i ≤ N →
      Fraction.le
        (stateNorm (stateSub
          (fineBlocks w h k s i) (coarseBlocks w h k s i)))
        (sourceBudget (fpower (kappa w h) k) (blockSource w h k s) i)
  | 0, _ => by
      have hz := stateSub_self_norm_zero s
      exact Fraction.le_of_equiv (by
        simpa only [fineBlocks, coarseBlocks, sourceBudget] using hz)
  | i + 1, hi => by
      have hiprev : i ≤ N := by omega
      have hprev := block_error_le_budget w h k s N hh hb hshort
        hcoarsePower i hiprev
      have hstep := block_error_step w h k s i hh hb hshort
      have hstate := coarseBlocks_state_le_two w h k s N hcoarsePower i hiprev
      have hcap := quadraticCap_double w (coarseBlocks w h k s i) s hstate k
      have h₂ : 0 ≤ (Fraction.mul h h).num :=
        Fraction.nonnegative_mul _ _ hh hh
      have hlocal := Fraction.mul_le_mul_nonnegative_left hcap
        (Fraction.mul h h) h₂
      have h₁ := Fraction.mul_le_mul_nonnegative_left hprev
        (fpower (kappa w h) k)
        (fpower_nonnegative _ (kappa_nonnegative w h) k)
      have hsum := Fraction.add_le_add h₁ hlocal
      have hbound := Fraction.magnitudes.le_trans hstep hsum
      simpa only [sourceBudget, blockSource] using hbound

def FullSmallTime (w d : Fraction) (N : Nat) : Prop :=
  Fraction.le
    (Fraction.mul (fullTime d N)
      (Fraction.add (Fraction.ofInt 1) w.abs)) halfThreshold

theorem kappa_duration_congr (w a b : Fraction)
    (hab : Fraction.equiv a b) :
    Fraction.equiv (kappa w a) (kappa w b) := by
  unfold kappa
  have ha := Fraction.abs_equiv hab
  exact Fraction.mul_equiv
    (Fraction.add_equiv (Fraction.equiv_refl _) ha)
    (Fraction.add_equiv (Fraction.equiv_refl _)
      (Fraction.mul_equiv ha (Fraction.equiv_refl _)))

theorem full_power_le_two (w d : Fraction) (N : Nat)
    (hd : 0 ≤ d.num) (hs : FullSmallTime w d N) :
    Fraction.le (fpower (kappa w d) N) (Fraction.ofInt 2) := by
  have htime := Fraction.mul_equiv (half_totalTime d N)
    (Fraction.equiv_refl (Fraction.add (Fraction.ofInt 1) w.abs))
  have hsmall : SmallTime w d.half N :=
    Fraction.le_equiv_left htime hs
  have hpower := coarse_power_le_two w d.half N hd hsmall
  have he := kappa_duration_congr w
    (Fraction.add d.half d.half) d (Fraction.half_add_self d)
  exact Fraction.le_equiv_left
    (Fraction.equiv_symm (fpower_congr he N)) hpower

theorem block_power_le_two (w h : Fraction) (k N : Nat)
    (hh : 0 ≤ h.num)
    (hs : FullSmallTime w (integerDuration h k) N) :
    Fraction.le
      (fpower (fpower (kappa w h) k) N) (Fraction.ofInt 2) := by
  have htime := Fraction.mul_equiv (integer_fullTime h k N)
    (Fraction.equiv_refl (Fraction.add (Fraction.ofInt 1) w.abs))
  have hsmall : FullSmallTime w h (k * N) :=
    Fraction.le_equiv_left htime hs
  have hpower := full_power_le_two w h (k * N) hh hsmall
  exact Fraction.le_equiv_left
    (fpower_integer_blocks (kappa w h) k N) hpower

/-- Accumulated comparison of `N` actual coarse cells of duration `k*h`
with `k*N` actual fine cells. The finite short-prefix inequalities ensure
each local split is inside the calibrated unit window. -/
theorem accumulated_integer_error (w h : Fraction) (k N : Nat)
    (s : Point × Point)
    (hh : 0 ≤ h.num) (hb : Fraction.le h.abs (Fraction.ofInt 1))
    (hshort : ∀ j, j ≤ k →
      Fraction.le (integerDuration h j).abs (Fraction.ofInt 1))
    (hs : FullSmallTime w (integerDuration h k) N) :
    Fraction.le
      (stateNorm (stateSub
        (fineBlocks w h k s N) (coarseBlocks w h k s N)))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (Fraction.ofInt (N : Int))
          (blockSource w h k s))) := by
  let r := fpower (kappa w h) k
  let C := blockSource w h k s
  have hd : 0 ≤ (integerDuration h k).num :=
    integerDuration_nonnegative h hh k
  have hcoarse := full_power_le_two w (integerDuration h k) N hd hs
  have hfine := block_power_le_two w h k N hh hs
  have h₀ := block_error_le_budget w h k s N hh hb hshort
    hcoarse N (Nat.le_refl N)
  have hr : 0 ≤ r.num := fpower_nonnegative _ (kappa_nonnegative w h) k
  have hone : Fraction.le (Fraction.ofInt 1) r :=
    one_le_fpower (kappa w h) (kappa_nonnegative w h)
      (one_le_kappa w h) k
  have hC : 0 ≤ C.num := blockSource_nonnegative w h k s hh
  have h₁ := sourceBudget_power r C hr hC hone N
  have hm₁ := Fraction.mul_le_mul_nonnegative hfine C hC
  have hm₂ := Fraction.mul_le_mul_nonnegative_left hm₁
    (Fraction.ofInt (N : Int)) (Int.ofNat_nonneg N)
  have h₁' := Fraction.le_equiv_right h₁
    (Fraction.mul_equiv (Fraction.equiv_refl _)
      (Fraction.mul_comm C (fpower r N)))
  have hbound := Fraction.magnitudes.le_trans h₀
    (Fraction.magnitudes.le_trans h₁' hm₂)
  apply Fraction.le_equiv_right hbound
  simp only [C, r, Fraction.equiv, Fraction.mul, Fraction.ofInt]
  ac_nf

theorem full_window_duration_le_one (w d : Fraction) (N : Nat)
    (hd : 0 ≤ d.num) (hN : 0 < N)
    (hs : FullSmallTime w d N) :
    Fraction.le d (Fraction.ofInt 1) := by
  have hc : Fraction.le (Fraction.ofInt 1)
      (Fraction.ofInt (N : Int)) := by
    unfold Fraction.le Fraction.ofInt
    dsimp
    simp only [Int.mul_one]
    exact Int.ofNat_le.mpr hN
  have hdtime₁ := Fraction.mul_le_mul_nonnegative hc d hd
  have hdtime : Fraction.le d (fullTime d N) := by
    apply Fraction.le_equiv_left (by
      simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp) hdtime₁
  have hfactor : Fraction.le (Fraction.ofInt 1)
      (Fraction.add (Fraction.ofInt 1) w.abs) :=
    Fraction.le_add_nonnegative _ _ (Fraction.abs_num_nonnegative w)
  have htime : 0 ≤ (fullTime d N).num :=
    Int.mul_nonneg (Int.ofNat_nonneg N) hd
  have hfactorTime := Fraction.mul_le_mul_nonnegative_left hfactor
    (fullTime d N) htime
  have htimeWeighted : Fraction.le (fullTime d N)
      (Fraction.mul (fullTime d N)
        (Fraction.add (Fraction.ofInt 1) w.abs)) := by
    have he : Fraction.equiv (fullTime d N)
        (Fraction.mul (fullTime d N) (Fraction.ofInt 1)) := by
      simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp
    exact Fraction.le_equiv_left he hfactorTime
  have hhalf : Fraction.le halfThreshold (Fraction.ofInt 1) := by
    unfold halfThreshold Fraction.le Fraction.ofInt
    decide
  exact Fraction.magnitudes.le_trans hdtime
    (Fraction.magnitudes.le_trans htimeWeighted
      (Fraction.magnitudes.le_trans hs hhalf))

theorem integer_window_short (w h : Fraction) (k N : Nat)
    (hh : 0 ≤ h.num) (hk : 0 < k) (hN : 0 < N)
    (hs : FullSmallTime w (integerDuration h k) N) :
    Fraction.le h.abs (Fraction.ofInt 1) ∧
      ∀ j, j ≤ k →
        Fraction.le (integerDuration h j).abs (Fraction.ofInt 1) := by
  let d := integerDuration h k
  have hd : 0 ≤ d.num := integerDuration_nonnegative h hh k
  have hdle := full_window_duration_le_one w d N hd hN hs
  have hfirst := integerDuration_le h hh 1 k hk
  have hfirstEq : Fraction.equiv (integerDuration h 1) h := by
    simp only [integerDuration, Fraction.equiv, Fraction.add, Fraction.ofInt]
    simp
  have hhle : Fraction.le h (Fraction.ofInt 1) :=
    Fraction.magnitudes.le_trans
      (Fraction.le_equiv_left (Fraction.equiv_symm hfirstEq) hfirst) hdle
  constructor
  · exact Fraction.le_equiv_left
      (Fraction.abs_of_nonnegative h hh) hhle
  · intro j hj
    have hprefix := integerDuration_le h hh j k hj
    have hjle := Fraction.magnitudes.le_trans hprefix hdle
    exact Fraction.le_equiv_left
      (Fraction.abs_of_nonnegative (integerDuration h j)
        (integerDuration_nonnegative h hh j)) hjle

/-- The positive-count small-window form needs no separate local
shortness assumptions. -/
theorem accumulated_integer_error_positive (w h : Fraction) (k N : Nat)
    (s : Point × Point)
    (hh : 0 ≤ h.num) (hk : 0 < k) (hN : 0 < N)
    (hs : FullSmallTime w (integerDuration h k) N) :
    Fraction.le
      (stateNorm (stateSub
        (fineBlocks w h k s N) (coarseBlocks w h k s N)))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (Fraction.ofInt (N : Int))
          (blockSource w h k s))) := by
  obtain ⟨hb, hshort⟩ := integer_window_short w h k N hh hk hN hs
  exact accumulated_integer_error w h k N s hh hb hshort hs

theorem integerFine_eq_run (w h : Fraction) (s : Point × Point) :
    (n : Nat) → integerFine w h s n = BoundedIteration.run (linearField w) h s n
  | 0 => rfl
  | n+1 => by
      simp only [integerFine, schedule_replicate_step, BoundedIteration.run]
      rw [← integerFine, integerFine_eq_run w h s n]
      rfl

theorem fineBlocks_eq_schedule (w h : Fraction) (k : Nat) (s : Point × Point) :
    (N : Nat) → fineBlocks w h k s N = integerFine w h s (k*N)
  | 0 => rfl
  | N+1 => by
      rw [fineBlocks, fineBlocks_eq_schedule w h k s N]
      simp only [integerFine_eq_run]
      rw [← BoundedIteration.run_add]
      congr 1

theorem coarseBlocks_eq_schedule (w h : Fraction) (k : Nat) (s : Point × Point) :
    (N : Nat) → coarseBlocks w h k s N = integerFine w (integerDuration h k) s N
  | 0 => rfl
  | N+1 => by
      rw [coarseBlocks, coarseBlocks_eq_schedule w h k s N]
      simp only [integerCoarse, integerFine, schedule_replicate_step]


end NewtonLimitDynamics.Polygon.HarmonicIntegerSubdivision
