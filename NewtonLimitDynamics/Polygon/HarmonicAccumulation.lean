import NewtonLimitDynamics.Polygon.HarmonicRefinement
import NewtonLimitDynamics.Polygon.HarmonicComparison

/-!
Finite global comparison of actual harmonic end-kick schedules with common
elapsed time. This is a coordinate L1 state budget only. It constructs no
limiting trajectory and makes no claim about the nonnegative region between
polygonal paths or the separate Kepler swept areas. The De Motu, 1687, and
1713 historical stages remain distinct from this modern rational estimate.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicAccumulation

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicRefinement
open HarmonicComparison
open PointBounds

private theorem add_equiv {a b c d : Fraction} (h : Fraction.equiv a b)
    (k : Fraction.equiv c d) :
    Fraction.equiv (Fraction.add a c) (Fraction.add b d) :=
  Fraction.equiv_trans (Fraction.add_equiv_right c h)
    (Fraction.equiv_trans (Fraction.add_comm b c)
      (Fraction.equiv_trans (Fraction.add_equiv_right b k) (Fraction.add_comm d b)))

private theorem mul_equiv {a b c d : Fraction} (h : Fraction.equiv a b)
    (k : Fraction.equiv c d) :
    Fraction.equiv (Fraction.mul a c) (Fraction.mul b d) :=
  Fraction.equiv_trans (Fraction.mul_comm a c)
    (Fraction.equiv_trans (Fraction.mul_equiv_left c h)
      (Fraction.equiv_trans (Fraction.mul_comm c b) (Fraction.mul_equiv_left b k)))

private theorem nonneg_add (a b : Fraction) (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    0 ≤ (Fraction.add a b).num := by
  unfold Fraction.add
  exact Int.add_nonneg
    (Int.mul_nonneg ha (Int.le_of_lt b.den_pos))
    (Int.mul_nonneg hb (Int.le_of_lt a.den_pos))

private theorem nonneg_mul (a b : Fraction) (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    0 ≤ (Fraction.mul a b).num := Int.mul_nonneg ha hb

private theorem le_add_nonneg (a b : Fraction) (hb : 0 ≤ b.num) :
    Fraction.le a (Fraction.add a b) := by
  unfold Fraction.le Fraction.add
  dsimp
  have hp := Int.mul_nonneg (Int.mul_nonneg hb (Int.le_of_lt a.den_pos))
    (Int.le_of_lt a.den_pos)
  simp only [Int.add_mul]
  have he : a.num * (a.den * b.den) = a.num * b.den * a.den := by ac_rfl
  rw [he]
  omega

private theorem point_le_state (s : Point × Point) :
    Fraction.le (pointNorm s.1) (stateNorm s) :=
  le_add_nonneg _ _ (pointNorm_nonnegative s.2)

private theorem velocity_le_state (s : Point × Point) :
    Fraction.le (pointNorm s.2) (stateNorm s) :=
  Fraction.le_equiv_right
    (le_add_nonneg _ _ (pointNorm_nonnegative s.1))
    (Fraction.add_comm (pointNorm s.2) (pointNorm s.1))

def localFactor (w h : Fraction) : Fraction :=
  Fraction.mul (Fraction.mul (Fraction.mul h.abs h.abs) w.abs)
    (Fraction.add (kappa w h) (Fraction.ofInt 1))

def coarseFactor (w h : Fraction) : Fraction := kappa w (Fraction.add h h)
def fineFactor (w h : Fraction) : Fraction := Fraction.mul (kappa w h) (kappa w h)

private def localA (w h : Fraction) : Fraction :=
  Fraction.mul (Fraction.mul h h) w
private def localC (w h : Fraction) : Fraction :=
  Fraction.mul (Fraction.mul (Fraction.mul h h) h) (Fraction.mul w w)

/-- The actual fine-minus-coarse state displacement, as represented rational
values. The first component is the position error, the second the velocity
error. -/
theorem local_error_identity (w h : Fraction) (s : Point × Point) :
    stateEquiv (stateSub (HarmonicRefinement.fine w h s) (HarmonicRefinement.coarse w h s))
      (pointScale (negF (localA w h)) (middle w h s),
        pointAdd (pointScale (localA w h) s.2)
          (pointScale (localC w h) (middle w h s))) := by
  constructor <;> constructor <;>
    simp only [stateSub, localA, localC, HarmonicRefinement.fine,
      HarmonicRefinement.coarse, middle,
      pointEquiv, pointSub, pointNeg, cell, linearField, negF,
      pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

private theorem localA_abs (w h : Fraction) :
    Fraction.equiv (localA w h).abs
      (Fraction.mul (Fraction.mul h.abs h.abs) w.abs) := by
  simp only [localA, Fraction.equiv, Fraction.abs, Fraction.mul,
    Int.natAbs_mul, Int.ofNat_mul]

private theorem neg_localA_abs (w h : Fraction) :
    Fraction.equiv (negF (localA w h)).abs
      (Fraction.mul (Fraction.mul h.abs h.abs) w.abs) :=
  Fraction.equiv_trans (Fraction.abs_neg (localA w h)) (localA_abs w h)

private theorem localC_abs (w h : Fraction) :
    Fraction.equiv (localC w h).abs
      (Fraction.mul (Fraction.mul (Fraction.mul h.abs h.abs) w.abs)
        (Fraction.mul h.abs w.abs)) := by
  simp only [localC, Fraction.equiv, Fraction.abs, Fraction.mul,
    Int.natAbs_mul, Int.ofNat_mul]
  ac_nf

private theorem middle_norm_bound (w h : Fraction) (s : Point × Point) :
    Fraction.le (pointNorm (middle w h s))
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) h.abs) (stateNorm s)) :=
  Fraction.magnitudes.le_trans (point_le_state (drift h s)) (drift_bound h s)

private def amplitude (w h : Fraction) : Fraction :=
  Fraction.mul (Fraction.mul h.abs h.abs) w.abs

private def kickMagnitude (w h : Fraction) : Fraction := Fraction.mul h.abs w.abs

private theorem amplitude_nonnegative (w h : Fraction) :
    0 ≤ (amplitude w h).num :=
  nonneg_mul _ _
    (nonneg_mul _ _ (Fraction.abs_num_nonnegative _) (Fraction.abs_num_nonnegative _))
    (Fraction.abs_num_nonnegative _)

private theorem kickMagnitude_nonnegative (w h : Fraction) :
    0 ≤ (kickMagnitude w h).num :=
  nonneg_mul _ _ (Fraction.abs_num_nonnegative _) (Fraction.abs_num_nonnegative _)

/-- Triangle and scaling estimate for the explicit local mismatch. -/
theorem local_error_expanded_bound (w h : Fraction) (s : Point × Point) :
    Fraction.le
      (stateNorm (stateSub (HarmonicRefinement.fine w h s)
        (HarmonicRefinement.coarse w h s)))
      (Fraction.add
        (Fraction.mul (amplitude w h) (pointNorm (middle w h s)))
        (Fraction.add
          (Fraction.mul (amplitude w h) (pointNorm s.2))
          (Fraction.mul (Fraction.mul (amplitude w h) (kickMagnitude w h))
            (pointNorm (middle w h s))))) := by
  let y := middle w h s
  let a := pointScale (negF (localA w h)) y
  let b := pointScale (localA w h) s.2
  let c := pointScale (localC w h) y
  have he := stateNorm_equiv (local_error_identity w h s)
  have ht := Fraction.add_le_add_left (pointNorm_add_le b c) (pointNorm a)
  have hp : Fraction.equiv (pointNorm a)
      (Fraction.mul (amplitude w h) (pointNorm y)) :=
    Fraction.equiv_trans (pointNorm_scale _ _)
      (mul_equiv (neg_localA_abs w h) (Fraction.equiv_refl _))
  have hv : Fraction.equiv (pointNorm b)
      (Fraction.mul (amplitude w h) (pointNorm s.2)) :=
    Fraction.equiv_trans (pointNorm_scale _ _)
      (mul_equiv (localA_abs w h) (Fraction.equiv_refl _))
  have hc : Fraction.equiv (pointNorm c)
      (Fraction.mul (Fraction.mul (amplitude w h) (kickMagnitude w h))
        (pointNorm y)) :=
    Fraction.equiv_trans (pointNorm_scale _ _)
      (mul_equiv (localC_abs w h) (Fraction.equiv_refl _))
  exact Fraction.le_equiv_left he
    (Fraction.le_equiv_right ht (add_equiv hp (add_equiv hv hc)))

/-- The local defect of two actual half-cells against one full cell is bounded
by `|h|²|w|(kappa+1)` times the current state magnitude. -/
theorem local_error_bound (w h : Fraction) (s : Point × Point) :
    Fraction.le
      (stateNorm (stateSub (HarmonicRefinement.fine w h s)
        (HarmonicRefinement.coarse w h s)))
      (Fraction.mul (localFactor w h) (stateNorm s)) := by
  have h₀ := local_error_expanded_bound w h s
  have hy := middle_norm_bound w h s
  have hv := velocity_le_state s
  have ha := amplitude_nonnegative w h
  have hat := nonneg_mul (amplitude w h) (kickMagnitude w h) ha
    (kickMagnitude_nonnegative w h)
  have h₁ := Fraction.mul_le_mul_nonnegative_left hy (amplitude w h) ha
  have h₂ := Fraction.mul_le_mul_nonnegative_left hv (amplitude w h) ha
  have h₃ := Fraction.mul_le_mul_nonnegative_left hy
    (Fraction.mul (amplitude w h) (kickMagnitude w h)) hat
  have hs := Fraction.add_le_add h₁ (Fraction.add_le_add h₂ h₃)
  have hchain := Fraction.magnitudes.le_trans h₀ hs
  apply Fraction.le_equiv_right hchain
  simp only [localFactor, amplitude, kickMagnitude, kappa, Fraction.equiv,
    Fraction.add, Fraction.mul, Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
  ac_nf


/-- The two actual endpoint recurrences, each block of duration `h+h`. -/
def coarseAt (w h : Fraction) (s : Point × Point) : Nat → Point × Point
  | 0 => s
  | n + 1 => HarmonicRefinement.coarse w h (coarseAt w h s n)

def fineAt (w h : Fraction) (s : Point × Point) : Nat → Point × Point
  | 0 => s
  | n + 1 => HarmonicRefinement.fine w h (fineAt w h s n)

def fineDurations (h : Fraction) : Nat → List Fraction
  | 0 => []
  | n + 1 => h :: h :: fineDurations h n

private theorem coarseAt_comm (w h : Fraction) (s : Point × Point) :
    (n : Nat) →
      coarseAt w h (HarmonicRefinement.coarse w h s) n =
        HarmonicRefinement.coarse w h (coarseAt w h s n)
  | 0 => rfl
  | n + 1 => by
      simp only [coarseAt]
      rw [coarseAt_comm w h s n]

private theorem fineAt_comm (w h : Fraction) (s : Point × Point) :
    (n : Nat) →
      fineAt w h (HarmonicRefinement.fine w h s) n =
        HarmonicRefinement.fine w h (fineAt w h s n)
  | 0 => rfl
  | n + 1 => by
      simp only [fineAt]
      rw [fineAt_comm w h s n]

/-- The coarse recurrence is the actual list schedule of `n` full cells. -/
theorem coarseAt_schedule (w h : Fraction) (s : Point × Point) :
    (n : Nat) →
      schedule (linearField w) (List.replicate n (Fraction.add h h)) s =
        coarseAt w h s n
  | 0 => rfl
  | n + 1 => by
      simp only [List.replicate_succ, schedule]
      change schedule (linearField w) (List.replicate n (Fraction.add h h))
        (HarmonicRefinement.coarse w h s) = coarseAt w h s (n + 1)
      rw [coarseAt_schedule w h (HarmonicRefinement.coarse w h s) n]
      exact coarseAt_comm w h s n

/-- The fine recurrence is the actual schedule of `2n` half-cells. -/
theorem fineAt_schedule (w h : Fraction) (s : Point × Point) :
    (n : Nat) →
      schedule (linearField w) (fineDurations h n) s = fineAt w h s n
  | 0 => rfl
  | n + 1 => by
      simp only [fineDurations, schedule]
      change schedule (linearField w) (fineDurations h n)
        (HarmonicRefinement.fine w h s) = fineAt w h s (n + 1)
      rw [fineAt_schedule w h (HarmonicRefinement.fine w h s) n]
      exact fineAt_comm w h s n

/-- Both actual lists have the same represented elapsed duration. -/
theorem schedules_common_time (w h : Fraction) :
    (n : Nat) →
      Fraction.equiv
        (elapsed (List.replicate n (Fraction.add h h)))
        (elapsed (fineDurations h n))
  | 0 => Fraction.equiv_refl _
  | n + 1 => by
      simp only [List.replicate_succ, fineDurations, elapsed]
      exact Fraction.equiv_trans
        (Fraction.add_assoc h h (elapsed (List.replicate n (Fraction.add h h))))
        (add_equiv (Fraction.equiv_refl h)
          (add_equiv (Fraction.equiv_refl h) (schedules_common_time w h n)))

/-- Finite rational powers, avoiding any completeness premise. -/
def fpower (a : Fraction) : Nat → Fraction
  | 0 => Fraction.ofInt 1
  | n + 1 => Fraction.mul a (fpower a n)

def errorBudget (w h : Fraction) (s : Point × Point) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | n + 1 =>
      Fraction.add (Fraction.mul (fineFactor w h) (errorBudget w h s n))
        (Fraction.mul (Fraction.mul (localFactor w h) (fpower (coarseFactor w h) n))
          (stateNorm s))

private theorem kappa_nonnegative (w h : Fraction) : 0 ≤ (kappa w h).num := by
  unfold kappa
  apply nonneg_mul
  · exact nonneg_add _ _ (by decide) (Fraction.abs_num_nonnegative _)
  · exact nonneg_add _ _ (by decide) (kickMagnitude_nonnegative w h)

private theorem localFactor_nonnegative (w h : Fraction) :
    0 ≤ (localFactor w h).num :=
  nonneg_mul _ _ (amplitude_nonnegative w h)
    (nonneg_add _ _ (kappa_nonnegative w h) (by decide))

private theorem fineFactor_nonnegative (w h : Fraction) :
    0 ≤ (fineFactor w h).num :=
  nonneg_mul _ _ (kappa_nonnegative w h) (kappa_nonnegative w h)

private theorem coarseFactor_nonnegative (w h : Fraction) :
    0 ≤ (coarseFactor w h).num := kappa_nonnegative w (Fraction.add h h)

theorem fpower_nonnegative (a : Fraction) (ha : 0 ≤ a.num) :
    (n : Nat) → 0 ≤ (fpower a n).num
  | 0 => by simp [fpower, Fraction.ofInt]
  | n + 1 => nonneg_mul _ _ ha (fpower_nonnegative a ha n)

theorem errorBudget_nonnegative (w h : Fraction) (s : Point × Point) :
    (n : Nat) → 0 ≤ (errorBudget w h s n).num
  | 0 => by simp [errorBudget, Fraction.ofInt]
  | n + 1 =>
      nonneg_add _ _
        (nonneg_mul _ _ (fineFactor_nonnegative w h)
          (errorBudget_nonnegative w h s n))
        (nonneg_mul _ _
          (nonneg_mul _ _ (localFactor_nonnegative w h)
            (fpower_nonnegative _ (coarseFactor_nonnegative w h) n))
          (stateNorm_nonnegative s))

/-- Two actual fine cells carry an input perturbation by at most `kappa²`. -/
theorem fine_perturbation (w h : Fraction) (s t : Point × Point) :
    Fraction.le
      (stateNorm (stateSub (HarmonicRefinement.fine w h s)
        (HarmonicRefinement.fine w h t)))
      (Fraction.mul (fineFactor w h) (stateNorm (stateSub s t))) := by
  have h₁ := cell_perturbation w h (cell (linearField w) h s)
    (cell (linearField w) h t)
  have h₂ := cell_perturbation w h s t
  have hm := Fraction.mul_le_mul_nonnegative_left h₂ (kappa w h)
    (kappa_nonnegative w h)
  have hc := Fraction.magnitudes.le_trans h₁ hm
  apply Fraction.le_equiv_right hc
  simp only [fineFactor, Fraction.equiv, Fraction.mul]
  ac_nf

private theorem stateSub_chain (a b c : Point × Point) :
    stateEquiv (stateSub a c)
      (pointAdd (stateSub a b).1 (stateSub b c).1,
        pointAdd (stateSub a b).2 (stateSub b c).2) := by
  constructor <;> constructor <;>
    simp only [stateSub, pointEquiv, pointSub, pointNeg, pointAdd,
      Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

private theorem stateSub_triangle (a b c : Point × Point) :
    Fraction.le (stateNorm (stateSub a c))
      (Fraction.add (stateNorm (stateSub a b)) (stateNorm (stateSub b c))) :=
  Fraction.le_equiv_left (stateNorm_equiv (stateSub_chain a b c))
    (stateNorm_add_le (stateSub a b) (stateSub b c))

/-- Every actual coarse state is bounded by `b^n` times the initial state
magnitude, with `b = kappa(w,h+h)`. -/
theorem coarse_norm_bound (w h : Fraction) (s : Point × Point) :
    (n : Nat) →
      Fraction.le (stateNorm (coarseAt w h s n))
        (Fraction.mul (fpower (coarseFactor w h) n) (stateNorm s))
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [coarseAt, fpower, Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp only [Int.one_mul, Int.mul_one]
  | n + 1 => by
      have hc := cell_bound w (Fraction.add h h) (coarseAt w h s n)
      have hi := coarse_norm_bound w h s n
      have hm := Fraction.mul_le_mul_nonnegative_left hi (coarseFactor w h)
        (coarseFactor_nonnegative w h)
      have hchain := Fraction.magnitudes.le_trans hc hm
      apply Fraction.le_equiv_right hchain
      simp only [coarseAt, fpower, coarseFactor, Fraction.equiv, Fraction.mul]
      ac_nf

private theorem stateSub_self_norm_zero (s : Point × Point) :
    Fraction.equiv (stateNorm (stateSub s s)) (Fraction.ofInt 0) := by
  have hz (a : Int) : (a + -a).natAbs = 0 := by omega
  simp only [stateNorm, stateSub, pointNorm, pointSub, pointNeg, pointAdd,
    Fraction.equiv, Fraction.abs, Fraction.add, Fraction.ofInt,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  simp only [hz, Int.ofNat_zero,
    Int.zero_mul, Int.mul_zero, Int.add_zero]

/-- The actual endpoints after `n` common blocks obey the recursively
constructed finite error budget. The recurrence uses the coarse state at each
block for the local defect and propagates the previous actual endpoint error
through two actual fine cells. -/
theorem actual_error_bound (w h : Fraction) (s : Point × Point) :
    (n : Nat) →
      Fraction.le (stateNorm (stateSub (fineAt w h s n) (coarseAt w h s n)))
        (errorBudget w h s n)
  | 0 => Fraction.le_of_equiv (stateSub_self_norm_zero s)
  | n + 1 => by
      let F := fineAt w h s n
      let C := coarseAt w h s n
      have ht := stateSub_triangle
        (HarmonicRefinement.fine w h F)
        (HarmonicRefinement.fine w h C)
        (HarmonicRefinement.coarse w h C)
      have hp := fine_perturbation w h F C
      have hl := local_error_bound w h C
      have hraw := Fraction.magnitudes.le_trans ht (Fraction.add_le_add hp hl)
      have hi := actual_error_bound w h s n
      have hc := coarse_norm_bound w h s n
      have hbi := Fraction.mul_le_mul_nonnegative_left hi (fineFactor w h)
        (fineFactor_nonnegative w h)
      have hbc := Fraction.mul_le_mul_nonnegative_left hc (localFactor w h)
        (localFactor_nonnegative w h)
      have hbudget := Fraction.add_le_add hbi hbc
      have hchain := Fraction.magnitudes.le_trans hraw hbudget
      apply Fraction.le_equiv_right hchain
      simp only [errorBudget, Fraction.equiv, Fraction.add, Fraction.mul]
      simp only [Int.add_mul, Int.mul_add]
      ac_nf

private def one : Fraction := ⟨1, 1, by decide⟩
private def zero : Fraction := ⟨0, 1, by decide⟩
private def half : Fraction := ⟨1, 2, by decide⟩
private def sample : Point × Point := ((one, zero), (zero, one))

private instance (s t : Point × Point) : Decidable (stateEquiv s t) :=
  inferInstanceAs (Decidable (pointEquiv s.1 t.1 ∧ pointEquiv s.2 t.2))

theorem sample_zero_blocks :
    stateEquiv (fineAt one zero sample 1) (coarseAt one zero sample 1) := by decide

theorem sample_zero_error :
    Fraction.equiv
      (stateNorm (stateSub (fineAt one zero sample 1) (coarseAt one zero sample 1)))
      zero := by decide

theorem sample_zero_budget :
    Fraction.equiv (errorBudget one zero sample 1) zero := by decide

theorem sample_initial_error :
    Fraction.equiv
      (stateNorm (stateSub (fineAt one half sample 0) (coarseAt one half sample 0)))
      zero := by decide

theorem sample_local_factor :
    Fraction.equiv (localFactor one half) ⟨13, 16, by decide⟩ := by decide

/-- Exact one-block state error. Its four component magnitudes are `1/4`,
`1/8`, `1/8`, and `5/16`; their sum is `13/16`. -/
theorem sample_one_block_error :
    Fraction.equiv
      (stateNorm (stateSub (fineAt one half sample 1) (coarseAt one half sample 1)))
      ⟨13, 16, by decide⟩ := by decide

theorem sample_one_block_budget :
    Fraction.equiv (errorBudget one half sample 1) ⟨13, 8, by decide⟩ := by decide

theorem sample_two_block_error :
    Fraction.equiv
      (stateNorm (stateSub (fineAt one half sample 2) (coarseAt one half sample 2)))
      ⟨173, 256, by decide⟩ := by decide

theorem sample_one_block_distinct :
    ¬ stateEquiv (fineAt one half sample 1) (coarseAt one half sample 1) := by decide

end NewtonLimitDynamics.Polygon.HarmonicAccumulation
