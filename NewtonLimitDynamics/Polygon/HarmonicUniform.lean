import NewtonLimitDynamics.Polygon.HarmonicAccumulation
import NewtonLimitDynamics.Common.FiniteGrowth

/-!
Mesh-uniform finite bounds for the actual harmonic coarse and fine schedules
under a small total-time condition. These coordinate L1 estimates provide
finite construction support only: no curve, completion, geometric region
between paths, or historical limiting step is constructed here.
The small-time threshold uses the chosen coordinate/unit calibration; it is
not a universal physical time bound.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicUniform

open NewtonLimitDynamics
open NewtonLimitDynamics.FiniteGrowth
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicRefinement
open HarmonicComparison
open HarmonicAccumulation
open PointBounds

private def halfThreshold : Fraction := ⟨1, 2, by decide⟩
private def denom (w h : Fraction) : Int := h.den * w.den
private def driftIncrement (w h : Fraction) : Int := h.num * w.den
private def kickIncrement (w h : Fraction) : Int := h.num * (w.num.natAbs : Int)

private theorem denom_pos (w h : Fraction) : 0 < denom w h :=
  Int.mul_pos h.den_pos w.den_pos

private theorem driftIncrement_nonnegative (w h : Fraction) (hh : 0 ≤ h.num) :
    0 ≤ driftIncrement w h :=
  Int.mul_nonneg hh (Int.le_of_lt w.den_pos)

private theorem kickIncrement_nonnegative (w h : Fraction) (hh : 0 ≤ h.num) :
    0 ≤ kickIncrement w h :=
  Int.mul_nonneg hh (Int.ofNat_nonneg _)

/-- `n` full cells have factors `(D+2A)/D` and `(D+2B)/D`. -/
def coarseWeights (w h : Fraction) : Nat → List Int
  | 0 => []
  | n + 1 => (2 * driftIncrement w h) :: (2 * kickIncrement w h) ::
      coarseWeights w h n

/-- `2n` half-cells have four factors per common block. -/
def fineWeights (w h : Fraction) : Nat → List Int
  | 0 => []
  | n + 1 => driftIncrement w h :: kickIncrement w h ::
      driftIncrement w h :: kickIncrement w h :: fineWeights w h n

private theorem coarseWeights_nonnegative (w h : Fraction) (hh : 0 ≤ h.num) :
    (n : Nat) → Nonnegative (coarseWeights w h n)
  | 0 => by simp [coarseWeights, Nonnegative]
  | n + 1 => by
      simp only [coarseWeights, Nonnegative, List.mem_cons]
      intro a ha
      rcases ha with rfl | rfl | ht
      · exact Int.mul_nonneg (by decide) (driftIncrement_nonnegative w h hh)
      · exact Int.mul_nonneg (by decide) (kickIncrement_nonnegative w h hh)
      · exact coarseWeights_nonnegative w h hh n a ht

private theorem fineWeights_nonnegative (w h : Fraction) (hh : 0 ≤ h.num) :
    (n : Nat) → Nonnegative (fineWeights w h n)
  | 0 => by simp [fineWeights, Nonnegative]
  | n + 1 => by
      simp only [fineWeights, Nonnegative, List.mem_cons]
      intro a ha
      rcases ha with rfl | rfl | rfl | rfl | ht
      · exact driftIncrement_nonnegative w h hh
      · exact kickIncrement_nonnegative w h hh
      · exact driftIncrement_nonnegative w h hh
      · exact kickIncrement_nonnegative w h hh
      · exact fineWeights_nonnegative w h hh n a ht

private theorem common_weight_sum (w h : Fraction) :
    (n : Nat) →
      weightSum (coarseWeights w h n) =
        weightSum (fineWeights w h n) ∧
      weightSum (fineWeights w h n) =
        2 * (n : Int) * (driftIncrement w h + kickIncrement w h)
  | 0 => by simp [coarseWeights, fineWeights, weightSum]
  | n + 1 => by
      obtain ⟨hc, hf⟩ := common_weight_sum w h n
      simp only [coarseWeights, fineWeights, weightSum, Int.natCast_add,
        Int.natCast_one]
      constructor
      · rw [hc]
        omega
      · rw [hf]
        simp only [Int.add_mul, Int.mul_add]
        omega

/-- Actual represented total time `T=2nh` and the smallness hypothesis
`T(1+|w|) ≤ 1/2`. Zero cell count and zero duration are included. -/
def totalTime (h : Fraction) (n : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt (2 * (n : Int))) h

def SmallTime (w h : Fraction) (n : Nat) : Prop :=
  Fraction.le
    (Fraction.mul (totalTime h n) (Fraction.add (Fraction.ofInt 1) w.abs)) halfThreshold

/-- The displayed total time is the elapsed time of the actual coarse list. -/
theorem coarse_elapsed_totalTime (h : Fraction) (n : Nat) :
    Fraction.equiv (elapsed (List.replicate n (Fraction.add h h)))
      (totalTime h n) := by
  induction n with
  | zero =>
      simp only [List.replicate_zero, elapsed, totalTime, Fraction.equiv,
        Fraction.mul, Fraction.ofInt]
      simp
  | succ n ih =>
      simp only [List.replicate_succ, elapsed]
      have ht := Fraction.equiv_trans
        (Fraction.add_comm (Fraction.add h h)
          (elapsed (List.replicate n (Fraction.add h h))))
        (Fraction.add_equiv_right (Fraction.add h h) ih)
      apply Fraction.equiv_trans ht
      simp only [totalTime, Fraction.equiv, Fraction.add, Fraction.mul,
        Fraction.ofInt, Int.natCast_add, Int.natCast_one,
        Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
      simp only [show (2 : Int) = 1 + 1 by rfl,
        Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
      ac_nf

/-- The fine list reaches the same displayed total time. -/
theorem fine_elapsed_totalTime (h : Fraction) (n : Nat) :
    Fraction.equiv (elapsed (fineDurations h n)) (totalTime h n) :=
  Fraction.equiv_trans
    (Fraction.equiv_symm (schedules_common_time (Fraction.ofInt 0) h n))
    (coarse_elapsed_totalTime h n)

private theorem smallTime_integer (w h : Fraction) (n : Nat)
    (hs : SmallTime w h n) :
    2 * (2 * (n : Int) * h.num * (w.den + (w.num.natAbs : Int))) ≤ denom w h := by
  unfold SmallTime totalTime halfThreshold Fraction.le Fraction.mul Fraction.add
    Fraction.ofInt Fraction.abs at hs
  dsimp at hs
  simp only [Int.mul_one, Int.one_mul, Int.add_zero] at hs
  change 2 * (2 * (n : Int) * h.num * (w.den + (w.num.natAbs : Int))) ≤
    h.den * w.den
  calc
    2 * (2 * (n : Int) * h.num * (w.den + (w.num.natAbs : Int))) =
        2 * (n : Int) * h.num * (w.den + (w.num.natAbs : Int)) * 2 := by ac_rfl
    _ ≤ h.den * w.den := hs

/-- The small-time condition is inherited by every earlier actual block. -/
theorem smallTime_prefix (w h : Fraction) (i n : Nat)
    (hh : 0 ≤ h.num) (hi : i ≤ n) (hs : SmallTime w h n) :
    SmallTime w h i := by
  have hn := smallTime_integer w h n hs
  have hcoef : 0 ≤ 4 * h.num * (w.den + (w.num.natAbs : Int)) := by
    exact Int.mul_nonneg
      (Int.mul_nonneg (by decide) hh)
      (Int.add_nonneg (Int.le_of_lt w.den_pos) (Int.ofNat_nonneg _))
  have hcast : (i : Int) ≤ (n : Int) := Int.ofNat_le.mpr hi
  have hm := Int.mul_le_mul_of_nonneg_right hcast hcoef
  have hpref :
      2 * (2 * (i : Int) * h.num * (w.den + (w.num.natAbs : Int))) ≤
        2 * (2 * (n : Int) * h.num * (w.den + (w.num.natAbs : Int))) := by
    calc
      _ = (i : Int) * (4 * h.num * (w.den + (w.num.natAbs : Int))) := by
        simp only [show (4 : Int) = 2 * 2 by rfl]
        ac_rfl
      _ ≤ (n : Int) * (4 * h.num * (w.den + (w.num.natAbs : Int))) := hm
      _ = _ := by
        simp only [show (4 : Int) = 2 * 2 by rfl]
        ac_rfl
  unfold SmallTime totalTime halfThreshold Fraction.le Fraction.mul Fraction.add
    Fraction.ofInt Fraction.abs
  dsimp
  simp only [Int.mul_one, Int.one_mul, Int.add_zero]
  calc
    2 * (i : Int) * h.num * (w.den + (w.num.natAbs : Int)) * 2 =
        2 * (2 * (i : Int) * h.num * (w.den + (w.num.natAbs : Int))) := by ac_rfl
    _ ≤ 2 * (2 * (n : Int) * h.num * (w.den + (w.num.natAbs : Int))) := hpref
    _ ≤ denom w h := hn

private theorem fineWeights_small (w h : Fraction) (n : Nat)
    (hs : SmallTime w h n) :
    2 * weightSum (fineWeights w h n) ≤ denom w h := by
  have hi := smallTime_integer w h n hs
  have hf := (common_weight_sum w h n).2
  calc
    2 * weightSum (fineWeights w h n) =
        2 * (2 * (n : Int) * h.num * (w.den + (w.num.natAbs : Int))) := by
      rw [hf]
      simp only [driftIncrement, kickIncrement, Int.mul_add]
      ac_nf
    _ ≤ denom w h := hi

private theorem coarseWeights_small (w h : Fraction) (n : Nat)
    (hs : SmallTime w h n) :
    2 * weightSum (coarseWeights w h n) ≤ denom w h := by
  rw [(common_weight_sum w h n).1]
  exact fineWeights_small w h n hs

private theorem mul_equiv {a b c d : Fraction} (h : Fraction.equiv a b)
    (k : Fraction.equiv c d) :
    Fraction.equiv (Fraction.mul a c) (Fraction.mul b d) :=
  Fraction.equiv_trans (Fraction.mul_comm a c)
    (Fraction.equiv_trans (Fraction.mul_equiv_left c h)
      (Fraction.equiv_trans (Fraction.mul_comm c b) (Fraction.mul_equiv_left b k)))

private theorem two_mul (x : Int) : 2 * x = x + x := by omega

private theorem coarse_block_equiv (w h : Fraction) (hh : 0 ≤ h.num) :
    Fraction.equiv
      (amplification (denom w h) (denom_pos w h)
        [2 * driftIncrement w h, 2 * kickIncrement w h])
      (coarseFactor w h) := by
  have hsum : 0 ≤ (Fraction.add h h).num := by
    unfold Fraction.add
    exact Int.add_nonneg
      (Int.mul_nonneg hh (Int.le_of_lt h.den_pos))
      (Int.mul_nonneg hh (Int.le_of_lt h.den_pos))
  simp only [amplification, factorProduct, denom, driftIncrement,
    kickIncrement, coarseFactor, kappa, Fraction.equiv, Fraction.abs,
    Fraction.add, Fraction.mul, Fraction.ofInt,
    List.length_cons, List.length_nil, Int.pow_succ,
    Int.pow_zero, Int.mul_one, Int.one_mul]
  change 0 ≤ h.num * h.den + h.num * h.den at hsum
  rw [Int.natAbs_of_nonneg hsum]
  simp only [two_mul, Int.add_mul, Int.mul_add]
  ac_nf

private theorem fine_block_equiv (w h : Fraction) (hh : 0 ≤ h.num) :
    Fraction.equiv
      (amplification (denom w h) (denom_pos w h)
        [driftIncrement w h, kickIncrement w h,
          driftIncrement w h, kickIncrement w h])
      (fineFactor w h) := by
  simp only [amplification, factorProduct, denom, driftIncrement,
    kickIncrement, fineFactor, kappa, Fraction.equiv, Fraction.abs,
    Fraction.add, Fraction.mul, Fraction.ofInt,
    List.length_cons, List.length_nil, Int.pow_succ,
    Int.pow_zero, Int.mul_one, Int.one_mul,
    Int.natAbs_of_nonneg hh]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

private theorem coarse_power_amplification (w h : Fraction) (hh : 0 ≤ h.num) :
    (n : Nat) →
      Fraction.equiv
        (amplification (denom w h) (denom_pos w h) (coarseWeights w h n))
        (fpower (coarseFactor w h) n)
  | 0 => amplification_empty _ _
  | n + 1 => by
      have ha := amplification_append (denom w h) (denom_pos w h)
        [2 * driftIncrement w h, 2 * kickIncrement w h] (coarseWeights w h n)
      have hb := coarse_block_equiv w h hh
      have hi := coarse_power_amplification w h hh n
      change Fraction.equiv
        (amplification (denom w h) (denom_pos w h)
          ([2 * driftIncrement w h, 2 * kickIncrement w h] ++ coarseWeights w h n))
        (Fraction.mul (coarseFactor w h) (fpower (coarseFactor w h) n))
      exact Fraction.equiv_trans ha (mul_equiv hb hi)

private theorem fine_power_amplification (w h : Fraction) (hh : 0 ≤ h.num) :
    (n : Nat) →
      Fraction.equiv
        (amplification (denom w h) (denom_pos w h) (fineWeights w h n))
        (fpower (fineFactor w h) n)
  | 0 => amplification_empty _ _
  | n + 1 => by
      have ha := amplification_append (denom w h) (denom_pos w h)
        [driftIncrement w h, kickIncrement w h,
          driftIncrement w h, kickIncrement w h] (fineWeights w h n)
      have hb := fine_block_equiv w h hh
      have hi := fine_power_amplification w h hh n
      change Fraction.equiv
        (amplification (denom w h) (denom_pos w h)
          ([driftIncrement w h, kickIncrement w h,
            driftIncrement w h, kickIncrement w h] ++ fineWeights w h n))
        (Fraction.mul (fineFactor w h) (fpower (fineFactor w h) n))
      exact Fraction.equiv_trans ha (mul_equiv hb hi)

/-- Uniform finite growth of the actual coarse amplification power. -/
theorem coarse_power_le_two (w h : Fraction) (n : Nat)
    (hh : 0 ≤ h.num) (hs : SmallTime w h n) :
    Fraction.le (fpower (coarseFactor w h) n) (Fraction.ofInt 2) :=
  Fraction.le_equiv_left (Fraction.equiv_symm (coarse_power_amplification w h hh n))
    (uniform_amplification (denom w h) (denom_pos w h) (coarseWeights w h n)
      (coarseWeights_nonnegative w h hh n) (coarseWeights_small w h n hs))

/-- Uniform finite growth of the actual two-cell perturbation power. -/
theorem fine_power_le_two (w h : Fraction) (n : Nat)
    (hh : 0 ≤ h.num) (hs : SmallTime w h n) :
    Fraction.le (fpower (fineFactor w h) n) (Fraction.ofInt 2) :=
  Fraction.le_equiv_left (Fraction.equiv_symm (fine_power_amplification w h hh n))
    (uniform_amplification (denom w h) (denom_pos w h) (fineWeights w h n)
      (fineWeights_nonnegative w h hh n) (fineWeights_small w h n hs))

/-- Actual coarse states stay inside twice the initial coordinate magnitude. -/
theorem coarse_state_le_two (w h : Fraction) (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) (hs : SmallTime w h n) :
    Fraction.le (stateNorm (coarseAt w h s n))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) :=
  Fraction.magnitudes.le_trans (coarse_norm_bound w h s n)
    (Fraction.mul_le_mul_nonnegative (coarse_power_le_two w h n hh hs)
      (stateNorm s) (stateNorm_nonnegative s))

private theorem fine_cell_bound (w h : Fraction) (s : Point × Point) :
    Fraction.le (stateNorm (HarmonicRefinement.fine w h s))
      (Fraction.mul (fineFactor w h) (stateNorm s)) := by
  have h₁ := cell_bound w h (cell (linearField w) h s)
  have h₂ := cell_bound w h s
  have hm := Fraction.mul_le_mul_nonnegative_left h₂ (kappa w h)
    (kappa_nonnegative w h)
  have hc := Fraction.magnitudes.le_trans h₁ hm
  apply Fraction.le_equiv_right hc
  simp only [fineFactor, Fraction.equiv, Fraction.mul]
  ac_nf

theorem fine_norm_bound (w h : Fraction) (s : Point × Point) :
    (n : Nat) →
      Fraction.le (stateNorm (fineAt w h s n))
        (Fraction.mul (fpower (fineFactor w h) n) (stateNorm s))
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [fineAt, fpower, Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp only [Int.one_mul, Int.mul_one]
  | n + 1 => by
      have hf := fine_cell_bound w h (fineAt w h s n)
      have hi := fine_norm_bound w h s n
      have hm := Fraction.mul_le_mul_nonnegative_left hi (fineFactor w h)
        (fineFactor_nonnegative w h)
      have hc := Fraction.magnitudes.le_trans hf hm
      apply Fraction.le_equiv_right hc
      simp only [fineAt, fpower, Fraction.equiv, Fraction.mul]
      ac_nf

theorem fine_state_le_two (w h : Fraction) (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) (hs : SmallTime w h n) :
    Fraction.le (stateNorm (fineAt w h s n))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) :=
  Fraction.magnitudes.le_trans (fine_norm_bound w h s n)
    (Fraction.mul_le_mul_nonnegative (fine_power_le_two w h n hh hs)
      (stateNorm s) (stateNorm_nonnegative s))

private theorem square_dominates_double (D a : Int) (ha : 0 ≤ a) :
    D * (D + 2 * a) ≤ (D + a) * (D + a) := by
  have hp := Int.mul_nonneg ha ha
  have he : (D + a) * (D + a) = D * (D + 2 * a) + a * a := by
    simp only [two_mul, Int.add_mul, Int.mul_add]
    ac_nf
  omega

private theorem block_product_order (D A B : Int) (hD : 0 < D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (D + 2 * A) * (D + 2 * B) * (D * D) ≤
      ((D + A) * (D + A)) * ((D + B) * (D + B)) := by
  have p := square_dominates_double D A hA
  have q := square_dominates_double D B hB
  have hp : 0 ≤ D * (D + 2 * A) :=
    Int.mul_nonneg (Int.le_of_lt hD)
      (Int.add_nonneg (Int.le_of_lt hD) (Int.mul_nonneg (by decide) hA))
  have hq : 0 ≤ (D + B) * (D + B) := by
    have hb : 0 ≤ D + B := Int.add_nonneg (Int.le_of_lt hD) hB
    exact Int.mul_nonneg hb hb
  have h₁ := Int.mul_le_mul_of_nonneg_right p hq
  have h₂ := Int.mul_le_mul_of_nonneg_left q hp
  calc
    (D + 2 * A) * (D + 2 * B) * (D * D) =
        (D * (D + 2 * A)) * (D * (D + 2 * B)) := by ac_rfl
    _ ≤ (D * (D + 2 * A)) * ((D + B) * (D + B)) := h₂
    _ ≤ ((D + A) * (D + A)) * ((D + B) * (D + B)) := h₁

private theorem block_amplification_order (w h : Fraction) (hh : 0 ≤ h.num) :
    Fraction.le
      (amplification (denom w h) (denom_pos w h)
        [2 * driftIncrement w h, 2 * kickIncrement w h])
      (amplification (denom w h) (denom_pos w h)
        [driftIncrement w h, kickIncrement w h,
          driftIncrement w h, kickIncrement w h]) := by
  have ho := block_product_order (denom w h) (driftIncrement w h)
    (kickIncrement w h) (denom_pos w h)
    (driftIncrement_nonnegative w h hh) (kickIncrement_nonnegative w h hh)
  unfold Fraction.le amplification
  simp only [factorProduct, List.length_cons, List.length_nil,
    Int.pow_succ, Int.pow_zero, Int.mul_one, Int.one_mul]
  have hd : 0 ≤ denom w h * denom w h :=
    Int.mul_nonneg (Int.le_of_lt (denom_pos w h)) (Int.le_of_lt (denom_pos w h))
  have hm := Int.mul_le_mul_of_nonneg_right ho hd
  calc
    _ =
        ((denom w h + 2 * driftIncrement w h) *
          (denom w h + 2 * kickIncrement w h) *
          (denom w h * denom w h)) * (denom w h * denom w h) := by ac_rfl
    _ ≤ ((denom w h + driftIncrement w h) *
          (denom w h + driftIncrement w h) *
          ((denom w h + kickIncrement w h) *
            (denom w h + kickIncrement w h))) *
          (denom w h * denom w h) := hm
    _ = _ := by ac_rfl

theorem coarseFactor_le_fineFactor (w h : Fraction) (hh : 0 ≤ h.num) :
    Fraction.le (coarseFactor w h) (fineFactor w h) :=
  Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.equiv_symm (coarse_block_equiv w h hh))
      (block_amplification_order w h hh))
    (fine_block_equiv w h hh)

private theorem one_le_one_add (a : Fraction) (ha : 0 ≤ a.num) :
    Fraction.le (Fraction.ofInt 1) (Fraction.add (Fraction.ofInt 1) a) := by
  unfold Fraction.le Fraction.add Fraction.ofInt
  dsimp
  have hp := Int.le_of_lt a.den_pos
  omega

private theorem one_le_kappa (w h : Fraction) :
    Fraction.le (Fraction.ofInt 1) (kappa w h) := by
  let u := Fraction.add (Fraction.ofInt 1) h.abs
  let v := Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs w.abs)
  have hu := one_le_one_add h.abs (Fraction.abs_num_nonnegative h)
  have hv := one_le_one_add (Fraction.mul h.abs w.abs)
    (Int.mul_nonneg (Fraction.abs_num_nonnegative h) (Fraction.abs_num_nonnegative w))
  have h₁ := Fraction.mul_le_mul_nonnegative hu (Fraction.ofInt 1) (by decide)
  have h₂ := Fraction.mul_le_mul_nonnegative_left hv u (by
    unfold u Fraction.add Fraction.ofInt
    dsimp
    have hp := h.abs.den_pos
    have hn := Fraction.abs_num_nonnegative h
    omega)
  have hc := Fraction.magnitudes.le_trans h₁ h₂
  apply Fraction.le_equiv_left (by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    decide) hc

private theorem one_le_fineFactor (w h : Fraction) :
    Fraction.le (Fraction.ofInt 1) (fineFactor w h) := by
  have hk := one_le_kappa w h
  have h₁ := Fraction.mul_le_mul_nonnegative hk (Fraction.ofInt 1) (by decide)
  have h₂ := Fraction.mul_le_mul_nonnegative_left hk (kappa w h)
    (kappa_nonnegative w h)
  have hc := Fraction.magnitudes.le_trans h₁ h₂
  apply Fraction.le_equiv_left (by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    decide) hc

private theorem fpower_monotone (a b : Fraction) (ha : 0 ≤ a.num)
    (hb : 0 ≤ b.num) (hab : Fraction.le a b) :
    (n : Nat) → Fraction.le (fpower a n) (fpower b n)
  | 0 => Fraction.magnitudes.le_refl _
  | n + 1 => by
      have h₁ := Fraction.mul_le_mul_nonnegative hab (fpower a n)
        (fpower_nonnegative a ha n)
      have h₂ := Fraction.mul_le_mul_nonnegative_left
        (fpower_monotone a b ha hb hab n) b hb
      exact Fraction.magnitudes.le_trans h₁ h₂

private theorem coarse_power_le_fine_power (w h : Fraction) (n : Nat)
    (hh : 0 ≤ h.num) :
    Fraction.le (fpower (coarseFactor w h) n) (fpower (fineFactor w h) n) :=
  fpower_monotone _ _ (kappa_nonnegative w (Fraction.add h h))
    (fineFactor_nonnegative w h) (coarseFactor_le_fineFactor w h hh) n

private def count (n : Nat) : Fraction := Fraction.ofInt (n : Int)

private def budgetCap (w h : Fraction) (s : Point × Point) (n : Nat) : Fraction :=
  Fraction.mul (count n)
    (Fraction.mul (localFactor w h)
      (Fraction.mul (fpower (fineFactor w h) n) (stateNorm s)))

private theorem budget_power_bound (w h : Fraction) (s : Point × Point)
    (hh : 0 ≤ h.num) :
    (n : Nat) → Fraction.le (errorBudget w h s n) (budgetCap w h s n)
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [errorBudget, budgetCap, count, fpower, Fraction.equiv,
        Fraction.ofInt, Fraction.mul]
      simp
  | n + 1 => by
      let d := localFactor w h
      let r := fineFactor w h
      let M := stateNorm s
      let X := Fraction.mul (Fraction.mul d (fpower r n)) M
      have hi := budget_power_bound w h s hh n
      have hr := fineFactor_nonnegative w h
      have hd := localFactor_nonnegative w h
      have hpow := fpower_nonnegative r hr n
      have hX : 0 ≤ X.num :=
        Int.mul_nonneg (Int.mul_nonneg hd hpow) (stateNorm_nonnegative s)
      have h₁ := Fraction.mul_le_mul_nonnegative_left hi r hr
      have hp := coarse_power_le_fine_power w h n hh
      have h₂a := Fraction.mul_le_mul_nonnegative_left hp d hd
      have h₂ := Fraction.mul_le_mul_nonnegative h₂a M (stateNorm_nonnegative s)
      have h₂b : Fraction.le X
          (Fraction.mul d (Fraction.mul (fpower r (n + 1)) M)) := by
        have hk := Fraction.mul_le_mul_nonnegative (one_le_fineFactor w h) X hX
        have he : Fraction.equiv X (Fraction.mul (Fraction.ofInt 1) X) := by
          simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
          simp
        have hk' := Fraction.le_equiv_left he hk
        apply Fraction.le_equiv_right hk'
        simp only [d, r, M, X, fpower, Fraction.equiv, Fraction.mul]
        ac_nf
      have h₂c := Fraction.magnitudes.le_trans h₂ h₂b
      have hsum := Fraction.add_le_add h₁ h₂c
      apply Fraction.le_equiv_right hsum
      simp only [d, r, M, errorBudget, budgetCap, count, fpower,
        Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
      simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.mul_add,
        Int.one_mul, Int.mul_one]
      ac_nf

private theorem budget_two_bound (w h : Fraction) (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) (hs : SmallTime w h n) :
    Fraction.le (errorBudget w h s n)
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (count n) (Fraction.mul (localFactor w h) (stateNorm s)))) := by
  have h₀ := budget_power_bound w h s hh n
  have hp := fine_power_le_two w h n hh hs
  have h₁ := Fraction.mul_le_mul_nonnegative hp (stateNorm s) (stateNorm_nonnegative s)
  have h₂ := Fraction.mul_le_mul_nonnegative_left h₁ (localFactor w h)
    (localFactor_nonnegative w h)
  have h₃ := Fraction.mul_le_mul_nonnegative_left h₂ (count n) (by
    unfold count Fraction.ofInt
    exact Int.ofNat_nonneg n)
  have hc := Fraction.magnitudes.le_trans h₀ h₃
  apply Fraction.le_equiv_right hc
  simp only [budgetCap, count, Fraction.equiv, Fraction.mul, Fraction.ofInt]
  ac_nf

private theorem one_le_power (a : Fraction) (ha : 0 ≤ a.num)
    (h1 : Fraction.le (Fraction.ofInt 1) a) :
    (n : Nat) → Fraction.le (Fraction.ofInt 1) (fpower a n)
  | 0 => Fraction.magnitudes.le_refl _
  | n + 1 => by
      have hi := one_le_power a ha h1 n
      have hm := Fraction.mul_le_mul_nonnegative h1 (fpower a n)
        (fpower_nonnegative a ha n)
      have he : Fraction.equiv (fpower a n)
          (Fraction.mul (Fraction.ofInt 1) (fpower a n)) := by
        simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
        simp
      exact Fraction.magnitudes.le_trans hi (Fraction.le_equiv_left he hm)

private theorem factor_le_power_succ (a : Fraction) (ha : 0 ≤ a.num)
    (h1 : Fraction.le (Fraction.ofInt 1) a) (n : Nat) :
    Fraction.le a (fpower a (n + 1)) := by
  have hp := one_le_power a ha h1 n
  have hm := Fraction.mul_le_mul_nonnegative_left hp a ha
  exact Fraction.le_equiv_left (by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    simp) hm

private theorem kappa_le_fineFactor (w h : Fraction) :
    Fraction.le (kappa w h) (fineFactor w h) := by
  have hk := one_le_kappa w h
  have hm := Fraction.mul_le_mul_nonnegative_left hk (kappa w h)
    (kappa_nonnegative w h)
  exact Fraction.le_equiv_left (by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    simp) hm

private theorem kappa_le_two_of_positive_blocks (w h : Fraction) (n : Nat)
    (hh : 0 ≤ h.num) (hs : SmallTime w h (n + 1)) :
    Fraction.le (kappa w h) (Fraction.ofInt 2) := by
  have h₁ := kappa_le_fineFactor w h
  have h₂ := factor_le_power_succ (fineFactor w h)
    (fineFactor_nonnegative w h) (one_le_fineFactor w h) n
  have h₃ := fine_power_le_two w h (n + 1) hh hs
  exact Fraction.magnitudes.le_trans (Fraction.magnitudes.le_trans h₁ h₂) h₃

private def meshAmplitude (w h : Fraction) : Fraction :=
  Fraction.mul (Fraction.mul h.abs h.abs) w.abs

private theorem meshAmplitude_nonnegative (w h : Fraction) :
    0 ≤ (meshAmplitude w h).num :=
  Int.mul_nonneg
    (Int.mul_nonneg (Fraction.abs_num_nonnegative h) (Fraction.abs_num_nonnegative h))
    (Fraction.abs_num_nonnegative w)

private theorem localFactor_le_three_amplitude (w h : Fraction) (n : Nat)
    (hh : 0 ≤ h.num) (hs : SmallTime w h (n + 1)) :
    Fraction.le (localFactor w h)
      (Fraction.mul (Fraction.ofInt 3) (meshAmplitude w h)) := by
  have hk := kappa_le_two_of_positive_blocks w h n hh hs
  have hplus := Fraction.add_le_add_right hk (Fraction.ofInt 1)
  have hm := Fraction.mul_le_mul_nonnegative hplus (meshAmplitude w h)
    (meshAmplitude_nonnegative w h)
  have hleft : Fraction.equiv (localFactor w h)
      (Fraction.mul (Fraction.add (kappa w h) (Fraction.ofInt 1))
        (meshAmplitude w h)) := by
    unfold localFactor meshAmplitude
    exact Fraction.mul_comm _ _
  have hright : Fraction.equiv
      (Fraction.mul (Fraction.add (Fraction.ofInt 2) (Fraction.ofInt 1))
        (meshAmplitude w h))
      (Fraction.mul (Fraction.ofInt 3) (meshAmplitude w h)) := by
    simp only [Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
    simp only [Int.mul_one, Int.one_mul]
    ac_nf
  exact Fraction.le_equiv_right (Fraction.le_equiv_left hleft hm) hright

/-- Uniform finite error at common total time `T=2nh`: actual fine and coarse
endpoints differ in coordinate L1 magnitude by at most `3*T*h*|w|*M`.
The hypothesis includes `h≥0` and `T*(1+|w|)≤1/2`. This is an endpoint
estimate, with no limiting curve or intervening-area assertion. -/
theorem actual_uniform_error (w h : Fraction) (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) (hs : SmallTime w h n) :
    Fraction.le
      (stateNorm (stateSub (fineAt w h s n) (coarseAt w h s n)))
      (Fraction.mul (Fraction.ofInt 3)
        (Fraction.mul (totalTime h n)
          (Fraction.mul h (Fraction.mul w.abs (stateNorm s))))) := by
  cases n with
  | zero =>
      have h₀ := actual_error_bound w h s 0
      apply Fraction.le_equiv_right h₀
      simp only [errorBudget, totalTime, Fraction.equiv,
        Fraction.mul, Fraction.ofInt]
      simp
  | succ m =>
      have h₀ := actual_error_bound w h s (m + 1)
      have h₁ := budget_two_bound w h s (m + 1) hh hs
      have hδ := localFactor_le_three_amplitude w h m hh hs
      have h₂ := Fraction.mul_le_mul_nonnegative hδ (stateNorm s)
        (stateNorm_nonnegative s)
      have h₃ := Fraction.mul_le_mul_nonnegative_left h₂ (count (m + 1)) (by
        unfold count Fraction.ofInt
        exact Int.ofNat_nonneg _)
      have h₄ := Fraction.mul_le_mul_nonnegative_left h₃ (Fraction.ofInt 2) (by decide)
      have hchain := Fraction.magnitudes.le_trans
        (Fraction.magnitudes.le_trans h₀ h₁) h₄
      apply Fraction.le_equiv_right hchain
      simp only [meshAmplitude, count, totalTime, Fraction.equiv,
        Fraction.mul, Fraction.abs, Fraction.ofInt,
        Int.natAbs_of_nonneg hh]
      ac_nf

private def one : Fraction := ⟨1, 1, by decide⟩
private def zero : Fraction := ⟨0, 1, by decide⟩
private def eighth : Fraction := ⟨1, 8, by decide⟩
private def sample : Point × Point := ((one, zero), (zero, one))

theorem sample_small_time : SmallTime one eighth 1 := by
  unfold SmallTime Fraction.le
  decide

theorem sample_total_time : Fraction.equiv (totalTime eighth 1) ⟨1, 4, by decide⟩ := by
  decide

theorem sample_power_bounds :
    Fraction.le (fpower (coarseFactor one eighth) 1) (Fraction.ofInt 2) ∧
      Fraction.le (fpower (fineFactor one eighth) 1) (Fraction.ofInt 2) :=
  ⟨coarse_power_le_two one eighth 1 (by decide) sample_small_time,
    fine_power_le_two one eighth 1 (by decide) sample_small_time⟩

theorem sample_actual_error :
    Fraction.equiv
      (stateNorm (stateSub (fineAt one eighth sample 1) (coarseAt one eighth sample 1)))
      ⟨145, 4096, by decide⟩ := by decide

theorem sample_uniform_rhs :
    Fraction.equiv
      (Fraction.mul (Fraction.ofInt 3)
        (Fraction.mul (totalTime eighth 1)
          (Fraction.mul eighth (Fraction.mul one.abs (stateNorm sample)))))
      ⟨3, 16, by decide⟩ := by decide

theorem sample_uniform_error :
    Fraction.le
      (stateNorm (stateSub (fineAt one eighth sample 1) (coarseAt one eighth sample 1)))
      (Fraction.mul (Fraction.ofInt 3)
        (Fraction.mul (totalTime eighth 1)
          (Fraction.mul eighth (Fraction.mul one.abs (stateNorm sample))))) :=
  actual_uniform_error one eighth sample 1 (by decide) sample_small_time

theorem sample_zero_blocks :
    Fraction.equiv
      (stateNorm (stateSub (fineAt one eighth sample 0) (coarseAt one eighth sample 0)))
      zero := by decide

theorem sample_zero_duration :
    Fraction.equiv
      (stateNorm (stateSub (fineAt one zero sample 1) (coarseAt one zero sample 1)))
      zero := by decide

/-- Without the total-time hypothesis, the claimed factor-two bound fails:
`w=h=n=1` gives `fineFactor^1=16`. -/
theorem false_unrestricted_power :
    ¬ Fraction.le (fpower (fineFactor one one) 1) (Fraction.ofInt 2) := by
  unfold Fraction.le
  decide

end NewtonLimitDynamics.Polygon.HarmonicUniform
