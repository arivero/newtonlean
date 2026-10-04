import NewtonLimitDynamics.Polygon.HarmonicDyadic

/-!
Finite comparisons of actual harmonic endpoint schedules at two rational times.
The cell counts agree; their durations differ. These estimates concern Cauchy
data only, without a limit point, trajectory, or intervening-area content.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicTimeComparison

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicComparison
open HarmonicAccumulation
open HarmonicUniform
open HarmonicDyadic
open PointBounds

def durationDifference (sigma tau : Fraction) : Fraction :=
  Fraction.add tau (negF sigma)

theorem cell_parameter_difference (w sigma tau : Fraction) (s : Point × Point) :
    stateEquiv
      (stateSub (cell (linearField w) tau s) (cell (linearField w) sigma s))
      (pointScale (durationDifference sigma tau) s.2,
        pointScale (negF (Fraction.mul (durationDifference sigma tau) w))
          (pointAdd s.1 (pointScale (Fraction.add sigma tau) s.2))) := by
  constructor <;> constructor <;>
    simp only [durationDifference, stateSub, pointEquiv, pointSub, pointNeg,
      cell, linearField, negF, pointAdd, pointScale, Fraction.equiv,
      Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

theorem cell_parameter_norm_formula (w sigma tau : Fraction) (s : Point × Point) :
    Fraction.equiv
      (stateNorm (stateSub (cell (linearField w) tau s)
        (cell (linearField w) sigma s)))
      (Fraction.mul (durationDifference sigma tau).abs
        (Fraction.add (pointNorm s.2)
          (Fraction.mul w.abs
            (pointNorm (pointAdd s.1
              (pointScale (Fraction.add sigma tau) s.2)))))) := by
  have hs := stateNorm_equiv (cell_parameter_difference w sigma tau s)
  apply Fraction.equiv_trans hs
  simp only [stateNorm, pointNorm, pointScale, negF, Fraction.equiv,
    Fraction.add, Fraction.mul, Fraction.abs, Int.natAbs_mul,
    Int.natAbs_neg, Int.ofNat_mul]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

private theorem add_num_nonnegative (a b : Fraction)
    (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    0 ≤ (Fraction.add a b).num :=
  Int.add_nonneg
    (Int.mul_nonneg ha (Int.le_of_lt b.den_pos))
    (Int.mul_nonneg hb (Int.le_of_lt a.den_pos))

theorem short_sum_point_bound (sigma tau : Fraction) (x v : Point)
    (hσ : 0 ≤ sigma.num) (hτ : 0 ≤ tau.num)
    (hsum : Fraction.le (Fraction.add sigma tau) (Fraction.ofInt 1)) :
    Fraction.le
      (pointNorm (pointAdd x (pointScale (Fraction.add sigma tau) v)))
      (Fraction.add (pointNorm x) (pointNorm v)) := by
  let q := Fraction.add sigma tau
  have hq : 0 ≤ q.num := add_num_nonnegative sigma tau hσ hτ
  have hs := pointNorm_scale q v
  have hqabs := Fraction.abs_of_nonnegative q hq
  have hscale : Fraction.le (pointNorm (pointScale q v)) (pointNorm v) := by
    have hq' : Fraction.le q.abs (Fraction.ofInt 1) :=
      Fraction.le_equiv_left hqabs hsum
    have hm := Fraction.mul_le_mul_nonnegative hq' (pointNorm v)
      (pointNorm_nonnegative v)
    apply Fraction.le_equiv_left hs
    apply Fraction.le_equiv_right hm
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    simp
  exact Fraction.magnitudes.le_trans (pointNorm_add_le x (pointScale q v))
    (Fraction.add_le_add_left hscale (pointNorm x))

private theorem scalar_local_bound (a b c : Fraction)
    (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) (hc : 0 ≤ c.num) :
    Fraction.le
      (Fraction.add b (Fraction.mul c (Fraction.add a b)))
      (Fraction.mul (Fraction.add (Fraction.ofInt 1)
        (Fraction.mul (Fraction.ofInt 2) c)) (Fraction.add a b)) := by
  let M := Fraction.add a b
  let cM := Fraction.mul c M
  have hbM : Fraction.le b M := by
    unfold Fraction.le M Fraction.add
    dsimp
    rw [Int.add_mul]
    have hnon := Int.mul_nonneg
      (Int.mul_nonneg ha (Int.le_of_lt b.den_pos)) (Int.le_of_lt b.den_pos)
    have he : b.num * (a.den * b.den) = b.num * a.den * b.den := by ac_rfl
    rw [he]
    omega
  have hfirst := Fraction.add_le_add_right hbM cM
  have hcM : 0 ≤ cM.num := Int.mul_nonneg hc (add_num_nonnegative a b ha hb)
  have hz : Fraction.le (Fraction.ofInt 0) cM := by
    unfold Fraction.le Fraction.ofInt
    dsimp
    simpa using hcM
  have hzero : Fraction.equiv (Fraction.add M (Fraction.ofInt 0)) M := by
    unfold Fraction.equiv Fraction.add Fraction.ofInt
    simp only [Int.mul_one, Int.zero_mul, Int.add_zero, Int.mul_zero]
  have hsecond : Fraction.le (Fraction.add M cM)
      (Fraction.add (Fraction.add M cM) cM) := by
    have hh := Fraction.add_le_add_left hz (Fraction.add M cM)
    exact Fraction.le_equiv_left (by
      simp only [Fraction.equiv, Fraction.add, Fraction.ofInt]
      simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
        Int.mul_one, Int.one_mul]) hh
  have he : Fraction.equiv (Fraction.add (Fraction.add M cM) cM)
      (Fraction.mul (Fraction.add (Fraction.ofInt 1)
        (Fraction.mul (Fraction.ofInt 2) c)) M) := by
    simp only [Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
    simp only [show (2 : Int) = 1 + 1 by rfl]
    simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
    simp only [cM, Fraction.mul]
    ac_nf
  exact Fraction.le_equiv_right (Fraction.magnitudes.le_trans hfirst hsecond) he

/-- The exact duration mismatch of one actual end-kick cell, bounded under a
short nonnegative combined duration. -/
theorem cell_parameter_bound (w sigma tau : Fraction) (s : Point × Point)
    (hσ : 0 ≤ sigma.num) (hτ : 0 ≤ tau.num)
    (hsum : Fraction.le (Fraction.add sigma tau) (Fraction.ofInt 1)) :
    Fraction.le
      (stateNorm (stateSub (cell (linearField w) tau s)
        (cell (linearField w) sigma s)))
      (Fraction.mul (durationDifference sigma tau).abs
        (Fraction.mul
          (Fraction.add (Fraction.ofInt 1)
            (Fraction.mul (Fraction.ofInt 2) w.abs)) (stateNorm s))) := by
  let d := durationDifference sigma tau
  have hp := short_sum_point_bound sigma tau s.1 s.2 hσ hτ hsum
  have hw := Fraction.mul_le_mul_nonnegative_left hp w.abs
    (Fraction.abs_num_nonnegative w)
  have ha := Fraction.add_le_add_left hw (pointNorm s.2)
  have hd := Fraction.mul_le_mul_nonnegative_left ha d.abs
    (Fraction.abs_num_nonnegative d)
  have hc := scalar_local_bound (pointNorm s.1) (pointNorm s.2) w.abs
    (pointNorm_nonnegative s.1) (pointNorm_nonnegative s.2)
    (Fraction.abs_num_nonnegative w)
  have hdc := Fraction.mul_le_mul_nonnegative_left hc d.abs
    (Fraction.abs_num_nonnegative d)
  have hf := cell_parameter_norm_formula w sigma tau s
  exact Fraction.le_equiv_right
    (Fraction.magnitudes.le_trans (Fraction.le_equiv_left hf hd) hdc)
    (by simp only [stateNorm]; exact Fraction.equiv_refl _)

def parameterFactor (w : Fraction) : Fraction :=
  Fraction.add (Fraction.ofInt 1)
    (Fraction.mul (Fraction.ofInt 2) w.abs)

def localParameterBudget (w sigma tau : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul (durationDifference sigma tau).abs
    (Fraction.mul (parameterFactor w)
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)))

def parameterErrorBudget (w hσ hτ : Fraction) (s : Point × Point) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | i + 1 =>
      Fraction.add
        (Fraction.mul (coarseFactor w hτ) (parameterErrorBudget w hσ hτ s i))
        (localParameterBudget w (Fraction.add hσ hσ) (Fraction.add hτ hτ) s)

private theorem parameterFactor_nonnegative (w : Fraction) :
    0 ≤ (parameterFactor w).num := by
  unfold parameterFactor
  exact add_num_nonnegative _ _ (by decide)
    (Int.mul_nonneg (by decide) (Fraction.abs_num_nonnegative w))

private theorem localParameterBudget_nonnegative (w sigma tau : Fraction)
    (s : Point × Point) :
    0 ≤ (localParameterBudget w sigma tau s).num := by
  unfold localParameterBudget
  exact Int.mul_nonneg (Fraction.abs_num_nonnegative _)
    (Int.mul_nonneg (parameterFactor_nonnegative w)
      (Int.mul_nonneg (by decide) (stateNorm_nonnegative s)))

private theorem parameterErrorBudget_nonnegative (w hσ hτ : Fraction)
    (s : Point × Point) :
    (i : Nat) → 0 ≤ (parameterErrorBudget w hσ hτ s i).num
  | 0 => by simp [parameterErrorBudget, Fraction.ofInt]
  | i + 1 =>
      add_num_nonnegative _ _
        (Int.mul_nonneg (kappa_nonnegative w (Fraction.add hτ hτ))
          (parameterErrorBudget_nonnegative w hσ hτ s i))
        (localParameterBudget_nonnegative w _ _ s)

theorem coarse_parameter_step (w sigma tau : Fraction) (a b : Point × Point)
    (hσ : 0 ≤ sigma.num) (hτ : 0 ≤ tau.num)
    (hsum : Fraction.le (Fraction.add sigma tau) (Fraction.ofInt 1)) :
    Fraction.le
      (stateNorm (stateSub (cell (linearField w) tau a)
        (cell (linearField w) sigma b)))
      (Fraction.add
        (Fraction.mul (kappa w tau) (stateNorm (stateSub a b)))
        (Fraction.mul (durationDifference sigma tau).abs
          (Fraction.mul (parameterFactor w) (stateNorm b)))) := by
  have htri := stateSub_triangle (cell (linearField w) tau a)
    (cell (linearField w) tau b) (cell (linearField w) sigma b)
  have h₁ := cell_perturbation w tau a b
  have h₂ := cell_parameter_bound w sigma tau b hσ hτ hsum
  exact Fraction.magnitudes.le_trans htri (Fraction.add_le_add h₁ h₂)

theorem actual_coarse_parameter_error (w hσ hτ : Fraction) (s : Point × Point)
    (n : Nat) (hhσ : 0 ≤ hσ.num) (hhτ : 0 ≤ hτ.num)
    (hsum : Fraction.le
      (Fraction.add (Fraction.add hσ hσ) (Fraction.add hτ hτ))
      (Fraction.ofInt 1)) (hsmall : SmallTime w hσ n) :
    (i : Nat) → i ≤ n →
      Fraction.le
        (stateNorm (stateSub (coarseAt w hτ s i) (coarseAt w hσ s i)))
        (parameterErrorBudget w hσ hτ s i)
  | 0, _ => Fraction.le_of_equiv (stateSub_self_norm_zero s)
  | i + 1, hi => by
      let sigma := Fraction.add hσ hσ
      let tau := Fraction.add hτ hτ
      let a := coarseAt w hτ s i
      let b := coarseAt w hσ s i
      have hi' : i ≤ n := by omega
      have hσnon := add_num_nonnegative hσ hσ hhσ hhσ
      have hτnon := add_num_nonnegative hτ hτ hhτ hhτ
      have hstep := coarse_parameter_step w sigma tau a b
        hσnon hτnon hsum
      have hprev := actual_coarse_parameter_error w hσ hτ s n hhσ hhτ
        hsum hsmall i hi'
      have hA := Fraction.mul_le_mul_nonnegative_left hprev
        (coarseFactor w hτ) (kappa_nonnegative w tau)
      have hprefix := coarse_state_le_two w hσ s i hhσ
        (smallTime_prefix w hσ i n hhσ hi' hsmall)
      have hB₁ := Fraction.mul_le_mul_nonnegative_left hprefix
        (parameterFactor w) (parameterFactor_nonnegative w)
      have hB₂ := Fraction.mul_le_mul_nonnegative_left hB₁
        (durationDifference sigma tau).abs
        (Fraction.abs_num_nonnegative _)
      have hsum' := Fraction.add_le_add hA hB₂
      have hchain := Fraction.magnitudes.le_trans hstep hsum'
      simpa only [coarseAt, HarmonicRefinement.coarse,
        parameterErrorBudget, localParameterBudget] using hchain

def parameterPowerBudget (w hσ hτ : Fraction) (s : Point × Point)
    (i : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt (i : Int))
    (Fraction.mul
      (localParameterBudget w (Fraction.add hσ hσ) (Fraction.add hτ hτ) s)
      (fpower (coarseFactor w hτ) i))

theorem parameter_budget_power (w hσ hτ : Fraction) (s : Point × Point) :
    (i : Nat) → Fraction.le (parameterErrorBudget w hσ hτ s i)
      (parameterPowerBudget w hσ hτ s i)
  | 0 => Fraction.le_of_equiv (by
      simp only [parameterErrorBudget, parameterPowerBudget, fpower,
        Fraction.equiv, Fraction.ofInt, Fraction.mul]
      simp)
  | i + 1 => by
      let d := localParameterBudget w (Fraction.add hσ hσ) (Fraction.add hτ hτ) s
      let b := coarseFactor w hτ
      have hd := localParameterBudget_nonnegative w
        (Fraction.add hσ hσ) (Fraction.add hτ hτ) s
      have hb := kappa_nonnegative w (Fraction.add hτ hτ)
      have h₁ := Fraction.mul_le_mul_nonnegative_left
        (parameter_budget_power w hσ hτ s i) b hb
      have hD : Fraction.le d (Fraction.mul d (fpower b (i + 1))) := by
        have hpow := one_le_power b hb (one_le_kappa w (Fraction.add hτ hτ))
          (i + 1)
        have hm := Fraction.mul_le_mul_nonnegative_left hpow d hd
        apply Fraction.le_equiv_left (by
          simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
          simp) hm
      have hsum := Fraction.add_le_add h₁ hD
      apply Fraction.le_equiv_right hsum
      simp only [d, b, parameterErrorBudget, parameterPowerBudget,
        fpower, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
      simp only [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.mul_add,
        Int.one_mul, Int.mul_one]
      ac_nf

theorem actual_coarse_parameter_uniform (w hσ hτ : Fraction)
    (s : Point × Point) (n : Nat)
    (hhσ : 0 ≤ hσ.num) (hhτ : 0 ≤ hτ.num)
    (hsum : Fraction.le
      (Fraction.add (Fraction.add hσ hσ) (Fraction.add hτ hτ))
      (Fraction.ofInt 1))
    (hsmallσ : SmallTime w hσ n) (hsmallτ : SmallTime w hτ n) :
    Fraction.le
      (stateNorm (stateSub (coarseAt w hτ s n) (coarseAt w hσ s n)))
      (Fraction.mul (Fraction.ofInt (2 * (n : Int)))
        (localParameterBudget w (Fraction.add hσ hσ)
          (Fraction.add hτ hτ) s)) := by
  let d := localParameterBudget w (Fraction.add hσ hσ)
    (Fraction.add hτ hτ) s
  have h₁ := actual_coarse_parameter_error w hσ hτ s n hhσ hhτ
    hsum hsmallσ n (Nat.le_refl n)
  have h₂ := parameter_budget_power w hσ hτ s n
  have hp := coarse_power_le_two w hτ n hhτ hsmallτ
  have hd := localParameterBudget_nonnegative w
    (Fraction.add hσ hσ) (Fraction.add hτ hτ) s
  have hm := Fraction.mul_le_mul_nonnegative_left hp d hd
  have hn := Fraction.mul_le_mul_nonnegative_left hm
    (Fraction.ofInt (n : Int)) (Int.ofNat_nonneg n)
  have hchain := Fraction.magnitudes.le_trans
    (Fraction.magnitudes.le_trans h₁ h₂) hn
  apply Fraction.le_equiv_right hchain
  simp only [parameterPowerBudget, d, Fraction.equiv, Fraction.mul,
    Fraction.ofInt]
  ac_nf

private def half : Fraction := ⟨1, 2, by decide⟩

theorem dyadic_time_le_half (w T : Fraction)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le T half := by
  have hw : 0 ≤ (w.num.natAbs : Int) := Int.ofNat_nonneg _
  have hnon : 0 ≤ 2 * T.num * (w.num.natAbs : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) hT) hw
  have hraw :
      2 * T.num * (w.den + (w.num.natAbs : Int)) ≤ T.den * w.den := by
    unfold DyadicSmallTime Fraction.le Fraction.mul Fraction.add Fraction.ofInt
      Fraction.abs at hs
    dsimp [HarmonicDyadic.halfThreshold] at hs
    simp only [Int.one_mul, Int.mul_one] at hs
    calc
      2 * T.num * (w.den + (w.num.natAbs : Int)) =
          T.num * (w.den + (w.num.natAbs : Int)) * 2 := by ac_rfl
      _ ≤ T.den * w.den := hs
  have hmul : (2 * T.num) * w.den ≤ T.den * w.den := by
    rw [Int.mul_add] at hraw
    omega
  have hbase := Int.le_of_mul_le_mul_right hmul w.den_pos
  unfold Fraction.le half
  dsimp
  omega

theorem duration_le_time (T : Fraction) (j : Nat) (hT : 0 ≤ T.num) :
    Fraction.le (duration T j) T := by
  have hpow : 1 ≤ (2 : Int) ^ j := by
    have h := two_pow_ge_succ j
    omega
  have hd := Int.mul_nonneg hT (Int.le_of_lt T.den_pos)
  have hm := Int.mul_le_mul_of_nonneg_left hpow hd
  unfold Fraction.le duration
  dsimp
  have he : T.num * (T.den * (2 : Int) ^ j) =
      (T.num * T.den) * (2 : Int) ^ j := by ac_rfl
  rw [he]
  omega

theorem short_duration_pair (w T U : Fraction) (j : Nat)
    (hT : 0 ≤ T.num) (hU : 0 ≤ U.num)
    (hsT : DyadicSmallTime w T) (hsU : DyadicSmallTime w U) :
    Fraction.le
      (Fraction.add
        (Fraction.add (duration T (j + 1)) (duration T (j + 1)))
        (Fraction.add (duration U (j + 1)) (duration U (j + 1))))
      (Fraction.ofInt 1) := by
  have hT' := duration_le_time T j hT
  have hU' := duration_le_time U j hU
  have hT'' := Fraction.le_equiv_left
    (Fraction.equiv_symm (duration_halving T j)) hT'
  have hU'' := Fraction.le_equiv_left
    (Fraction.equiv_symm (duration_halving U j)) hU'
  have hhalf := Fraction.add_le_add (dyadic_time_le_half w T hT hsT)
    (dyadic_time_le_half w U hU hsU)
  have hsum := Fraction.magnitudes.le_trans
    (Fraction.add_le_add hT'' hU'') hhalf
  apply Fraction.le_equiv_right hsum
  decide

/-- The common count cancels the per-cell signed duration difference in
rational value, even though the representatives differ. -/
theorem count_duration_difference (T U : Fraction) (j : Nat) :
    Fraction.equiv
      (Fraction.mul (Fraction.ofInt (blocks j : Int))
        (durationDifference
          (Fraction.add (duration T (j + 1)) (duration T (j + 1)))
          (Fraction.add (duration U (j + 1)) (duration U (j + 1)))))
      (durationDifference T U) := by
  have hdur : Fraction.equiv
      (durationDifference
        (Fraction.add (duration T (j + 1)) (duration T (j + 1)))
        (Fraction.add (duration U (j + 1)) (duration U (j + 1))))
      (durationDifference (duration T j) (duration U j)) :=
    HarmonicDyadic.add_equiv
      (Fraction.equiv_symm (duration_halving U j))
      (HarmonicDyadic.neg_equiv
        (Fraction.equiv_symm (duration_halving T j)))
  have hm := HarmonicDyadic.mul_equiv
    (Fraction.equiv_refl (Fraction.ofInt (blocks j : Int))) hdur
  apply Fraction.equiv_trans hm
  simp only [blocks, duration, durationDifference, negF, Fraction.equiv,
    Fraction.ofInt, Fraction.add, Fraction.mul, Int.natCast_pow]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.one_mul, Int.mul_one]
  ac_nf

theorem count_abs_duration_difference (T U : Fraction) (j : Nat) :
    Fraction.equiv
      (Fraction.mul (Fraction.ofInt (blocks j : Int))
        (durationDifference
          (Fraction.add (duration T (j + 1)) (duration T (j + 1)))
          (Fraction.add (duration U (j + 1)) (duration U (j + 1)))).abs)
      (durationDifference T U).abs := by
  have hs := count_duration_difference T U j
  have habs := Fraction.abs_equiv hs
  have hm := Fraction.abs_mul (Fraction.ofInt (blocks j : Int))
    (durationDifference
      (Fraction.add (duration T (j + 1)) (duration T (j + 1)))
      (Fraction.add (duration U (j + 1)) (duration U (j + 1))))
  have hcount : Fraction.equiv (Fraction.ofInt (blocks j : Int)).abs
      (Fraction.ofInt (blocks j : Int)) :=
    Fraction.abs_of_nonnegative _ (Int.ofNat_nonneg _)
  have hmul := HarmonicDyadic.mul_equiv hcount
    (Fraction.equiv_refl
      (durationDifference
        (Fraction.add (duration T (j + 1)) (duration T (j + 1)))
        (Fraction.add (duration U (j + 1)) (duration U (j + 1)))).abs)
  exact Fraction.equiv_trans (Fraction.equiv_symm hmul)
    (Fraction.equiv_trans (Fraction.equiv_symm hm) habs)

def timeLipschitz (w : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul (Fraction.ofInt 4)
    (Fraction.mul (parameterFactor w) (stateNorm s))

/-- Uniform rational-time variation of the actual dyadic endpoint schedules.
The same level has the same count and two different cell durations. -/
theorem endpoint_time_bound (w T U : Fraction) (s : Point × Point) (j : Nat)
    (hT : 0 ≤ T.num) (hU : 0 ≤ U.num)
    (hsT : DyadicSmallTime w T) (hsU : DyadicSmallTime w U) :
    Fraction.le
      (stateNorm (stateSub (endpoint w U s j) (endpoint w T s j)))
      (Fraction.mul (timeLipschitz w s) (durationDifference T U).abs) := by
  let hσ := duration T (j + 1)
  let hτ := duration U (j + 1)
  let n := blocks j
  have hσnon : 0 ≤ hσ.num := hT
  have hτnon : 0 ≤ hτ.num := hU
  have hbound := actual_coarse_parameter_uniform w hσ hτ s n
    hσnon hτnon (short_duration_pair w T U j hT hU hsT hsU)
    (dyadic_smallTime w T j hsT) (dyadic_smallTime w U j hsU)
  have he : stateEquiv
      (stateSub (endpoint w U s j) (endpoint w T s j))
      (stateSub (coarseAt w hτ s n) (coarseAt w hσ s n)) :=
    stateSub_congr (endpoint_coarse w U s j) (endpoint_coarse w T s j)
  have hfirst := Fraction.le_equiv_left (stateNorm_equiv he) hbound
  let d := (durationDifference
    (Fraction.add hσ hσ) (Fraction.add hτ hτ)).abs
  have hrewrite : Fraction.equiv
      (Fraction.mul (Fraction.ofInt (2 * (n : Int)))
        (localParameterBudget w (Fraction.add hσ hσ)
          (Fraction.add hτ hτ) s))
      (Fraction.mul
        (Fraction.mul (Fraction.ofInt 4)
          (Fraction.mul (parameterFactor w) (stateNorm s)))
        (Fraction.mul (Fraction.ofInt (n : Int)) d)) := by
    simp only [localParameterBudget, d, Fraction.equiv, Fraction.mul,
      Fraction.ofInt]
    ac_nf
  have hc := count_abs_duration_difference T U j
  have hsecond := HarmonicDyadic.mul_equiv
    (Fraction.equiv_refl (timeLipschitz w s)) hc
  exact Fraction.le_equiv_right hfirst
    (Fraction.equiv_trans hrewrite hsecond)

theorem timeLipschitz_nonnegative (w : Fraction) (s : Point × Point) :
    0 ≤ (timeLipschitz w s).num :=
  Int.mul_nonneg (by decide)
    (Int.mul_nonneg (parameterFactor_nonnegative w) (stateNorm_nonnegative s))

private def timeDenominator (w : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (timeLipschitz w s) (Fraction.ofInt 1)

private theorem timeDenominator_positive (w : Fraction) (s : Point × Point) :
    0 < (timeDenominator w s).num := by
  unfold timeDenominator Fraction.add Fraction.ofInt
  dsimp
  have hL := timeLipschitz_nonnegative w s
  have hd := (timeLipschitz w s).den_pos
  omega

/-- Rational delta equal in value to `eps/(L+1)`. The added one makes the
choice positive even when the initial state magnitude is zero. -/
def timeDelta (w : Fraction) (s : Point × Point) (eps : Fraction) : Fraction :=
  ⟨eps.num * (timeDenominator w s).den,
    eps.den * (timeDenominator w s).num,
    Int.mul_pos eps.den_pos (timeDenominator_positive w s)⟩

theorem timeDelta_positive (w : Fraction) (s : Point × Point) (eps : Fraction)
    (heps : 0 < eps.num) : 0 < (timeDelta w s eps).num :=
  Int.mul_pos heps (timeDenominator w s).den_pos

private theorem mul_lt_mul_positive_left {a b : Fraction}
    (hab : Fraction.lt a b) (c : Fraction) (hc : 0 < c.num) :
    Fraction.lt (Fraction.mul c a) (Fraction.mul c b) := by
  have hm := Int.mul_lt_mul_of_pos_right hab
    (Int.mul_pos hc c.den_pos)
  unfold Fraction.lt Fraction.mul at *
  dsimp at *
  have h₁ : c.num * a.num * (c.den * b.den) =
      (a.num * b.den) * (c.num * c.den) := by ac_rfl
  have h₂ : c.num * b.num * (c.den * a.den) =
      (b.num * a.den) * (c.num * c.den) := by ac_rfl
  rw [h₁, h₂]
  exact hm

private theorem timeLipschitz_le_denominator (w : Fraction) (s : Point × Point) :
    Fraction.le (timeLipschitz w s) (timeDenominator w s) := by
  unfold timeDenominator Fraction.le Fraction.add Fraction.ofInt
  dsimp
  have hd := (timeLipschitz w s).den_pos
  have hsq : 0 ≤ (timeLipschitz w s).den * (timeLipschitz w s).den :=
    Int.mul_nonneg (Int.le_of_lt hd) (Int.le_of_lt hd)
  simp only [Int.one_mul, Int.mul_one, Int.add_mul]
  omega

private theorem delta_product_equiv (w : Fraction) (s : Point × Point)
    (eps : Fraction) :
    Fraction.equiv
      (Fraction.mul (timeDenominator w s) (timeDelta w s eps)) eps := by
  unfold Fraction.equiv Fraction.mul timeDelta
  dsimp
  ac_nf

theorem parameter_delta_control (w : Fraction) (s : Point × Point)
    (eps d : Fraction) (_heps : 0 < eps.num)
    (hd : 0 ≤ d.num) (hdelta : Fraction.lt d (timeDelta w s eps)) :
    Fraction.lt (Fraction.mul (timeLipschitz w s) d) eps := by
  have hweak := Fraction.mul_le_mul_nonnegative
    (timeLipschitz_le_denominator w s) d hd
  have hstrict := mul_lt_mul_positive_left hdelta
    (timeDenominator w s) (timeDenominator_positive w s)
  have htrans := Fraction.magnitudes.lt_of_le_lt hweak hstrict
  have heq := delta_product_equiv w s eps
  exact Fraction.magnitudes.lt_of_lt_le htrans
    ((Fraction.equiv_iff_mutual_le _ _).mp heq).1

def ShortRationalTime (w : Fraction) :=
  {T : Fraction // 0 ≤ T.num ∧ DyadicSmallTime w T}

/-- Each admissible rational time is mapped to its derived endpoint Cauchy
name. This map does not realize a point of a completed state space. -/
def timeName (w : Fraction) (s : Point × Point)
    (T : ShortRationalTime w) : EndpointCauchyName :=
  endpointName w T.val s T.property.1 T.property.2

/-- One explicit delta controls every approximant level at once. -/
theorem timeName_uniform_continuity (w : Fraction) (s : Point × Point)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ delta : Fraction, 0 < delta.num ∧
      ∀ T U : ShortRationalTime w,
        Fraction.lt (durationDifference T.val U.val).abs delta →
        ∀ j : Nat,
          Fraction.lt
            (stateNorm (stateSub ((timeName w s U).approx j)
              ((timeName w s T).approx j))) eps := by
  refine ⟨timeDelta w s eps, timeDelta_positive w s eps heps, ?_⟩
  intro T U hdelta j
  have hb := endpoint_time_bound w T.val U.val s j
    T.property.1 U.property.1 T.property.2 U.property.2
  have hd := Fraction.abs_num_nonnegative (durationDifference T.val U.val)
  have hstrict := parameter_delta_control w s eps
    (durationDifference T.val U.val).abs heps hd hdelta
  exact Fraction.magnitudes.lt_of_le_lt hb hstrict

theorem same_time_error_zero (w T : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv
      (stateNorm (stateSub (endpoint w T s j) (endpoint w T s j)))
      (Fraction.ofInt 0) :=
  stateSub_self_norm_zero _

private def zeroFraction : Fraction := ⟨0, 1, by decide⟩
private def zeroState : Point × Point :=
  ((zeroFraction, zeroFraction), (zeroFraction, zeroFraction))

theorem zero_state_error_zero (w T U : Fraction) (j : Nat)
    (hT : 0 ≤ T.num) (hU : 0 ≤ U.num)
    (hsT : DyadicSmallTime w T) (hsU : DyadicSmallTime w U) :
    Fraction.equiv
      (stateNorm (stateSub (endpoint w U zeroState j)
        (endpoint w T zeroState j))) (Fraction.ofInt 0) := by
  have hb := endpoint_time_bound w T U zeroState j hT hU hsT hsU
  have hz : Fraction.equiv
      (Fraction.mul (timeLipschitz w zeroState)
        (durationDifference T U).abs) (Fraction.ofInt 0) := by
    simp only [timeLipschitz, parameterFactor, zeroState,
      zeroFraction, stateNorm, pointNorm, Fraction.equiv,
      Fraction.abs, Fraction.add, Fraction.mul, Fraction.ofInt]
    simp
  have hle := Fraction.le_equiv_right hb hz
  have hother : Fraction.le (Fraction.ofInt 0)
      (stateNorm (stateSub (endpoint w U zeroState j)
        (endpoint w T zeroState j))) := by
    unfold Fraction.le Fraction.ofInt
    dsimp
    simp only [Int.zero_mul, Int.mul_one]
    exact stateNorm_nonnegative _
  exact (Fraction.equiv_iff_mutual_le _ _).mpr ⟨hle, hother⟩

private def sampleOne : Fraction := ⟨1, 1, by decide⟩
private def sampleZero : Fraction := ⟨0, 1, by decide⟩
private def sampleQuarter : Fraction := ⟨1, 4, by decide⟩
private def sampleEighth : Fraction := ⟨1, 8, by decide⟩
private def sampleState : Point × Point :=
  ((sampleOne, sampleZero), (sampleZero, sampleOne))

theorem sample_short_times :
    DyadicSmallTime sampleOne sampleQuarter ∧
      DyadicSmallTime sampleOne sampleEighth := by
  constructor <;> unfold DyadicSmallTime Fraction.le <;> decide

theorem sample_parameter_error :
    Fraction.equiv
      (stateNorm (stateSub
        (endpoint sampleOne sampleEighth sampleState 0)
        (endpoint sampleOne sampleQuarter sampleState 0)))
      ⟨19, 64, by decide⟩ := by decide

theorem sample_time_lipschitz :
    Fraction.equiv (timeLipschitz sampleOne sampleState)
      (Fraction.ofInt 24) := by decide

theorem sample_time_budget :
    Fraction.equiv
      (Fraction.mul (timeLipschitz sampleOne sampleState)
        (durationDifference sampleQuarter sampleEighth).abs)
      (Fraction.ofInt 3) := by decide

theorem sample_parameter_bound :
    Fraction.le
      (stateNorm (stateSub
        (endpoint sampleOne sampleEighth sampleState 0)
        (endpoint sampleOne sampleQuarter sampleState 0)))
      (Fraction.mul (timeLipschitz sampleOne sampleState)
        (durationDifference sampleQuarter sampleEighth).abs) :=
  endpoint_time_bound sampleOne sampleQuarter sampleEighth sampleState 0
    (by decide) (by decide) sample_short_times.1 sample_short_times.2

end NewtonLimitDynamics.Polygon.HarmonicTimeComparison
