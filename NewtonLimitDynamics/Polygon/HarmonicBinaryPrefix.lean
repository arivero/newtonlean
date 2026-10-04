import NewtonLimitDynamics.Polygon.HarmonicTimeComparison

/-!
Actual intermediate prefixes of one dyadic harmonic polygon family, indexed
by binary addresses. The approximants are finite schedules only. No completed
point, continuum trajectory, or region between polygon and trajectory is
assumed; Kepler swept area remains a distinct quantity.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicBinaryPrefix

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicComparison
open HarmonicAccumulation
open HarmonicUniform
open HarmonicDyadic
open HarmonicTimeComparison
open PointBounds

def bit (b : Nat → Bool) (j : Nat) : Nat := if b j then 1 else 0

def ticks (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | j + 1 => 2 * ticks b j + bit b j

def prefixState (b : Nat → Bool) (w T : Fraction) (s : Point × Point)
    (j : Nat) : Point × Point :=
  schedule (linearField w) (List.replicate (ticks b j) (duration T j)) s

theorem bit_le_one (b : Nat → Bool) (j : Nat) : bit b j ≤ 1 := by
  unfold bit
  split <;> omega

theorem ticks_lt_blocks (b : Nat → Bool) :
    (j : Nat) → ticks b j < blocks j
  | 0 => by simp [ticks, blocks]
  | j + 1 => by
      have ih := ticks_lt_blocks b j
      have hb := bit_le_one b j
      rw [ticks, blocks_succ]
      omega

theorem ticks_le_blocks (b : Nat → Bool) (j : Nat) :
    ticks b j ≤ blocks j := Nat.le_of_lt (ticks_lt_blocks b j)

theorem ticks_next (b : Nat → Bool) (j : Nat) :
    ticks b (j + 1) = ticks b j + ticks b j + bit b j := by
  simp only [ticks]
  omega

theorem prefix_coarse (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat) :
    stateEquiv (prefixState b w T s j)
      (coarseAt w (duration T (j + 1)) s (ticks b j)) := by
  let h := duration T (j + 1)
  have hc := schedule_replicate_congr w (duration T j) (Fraction.add h h)
    (duration_halving T j) (ticks b j) s s
    ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩
  simpa only [prefixState, coarseAt_schedule] using hc

theorem prefix_state_le_two (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le (stateNorm (prefixState b w T s j))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) := by
  let h := duration T (j + 1)
  have hprefix := smallTime_prefix w h (ticks b j) (blocks j) hT
    (ticks_le_blocks b j) (dyadic_smallTime w T j hs)
  have hc := coarse_state_le_two w h s (ticks b j) hT hprefix
  exact Fraction.le_equiv_left
    (stateNorm_equiv (prefix_coarse b w T s j)) hc

theorem elapsed_replicate (d : Fraction) :
    (n : Nat) → Fraction.equiv (elapsed (List.replicate n d))
      (Fraction.mul (Fraction.ofInt (n : Int)) d)
  | 0 => by
      simp only [elapsed, List.replicate_zero, Fraction.equiv,
        Fraction.ofInt, Fraction.mul]
      simp
  | n + 1 => by
      have ih := elapsed_replicate d n
      have he := HarmonicDyadic.add_equiv (Fraction.equiv_refl d) ih
      apply Fraction.equiv_trans he
      simp only [elapsed, List.replicate_succ, Fraction.equiv,
        Fraction.add, Fraction.mul, Fraction.ofInt, Int.natCast_add]
      simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
      ac_nf

theorem prefix_elapsed (b : Nat → Bool) (T : Fraction) (j : Nat) :
    Fraction.equiv
      (elapsed (List.replicate (ticks b j) (duration T j)))
      (Fraction.mul (Fraction.ofInt (ticks b j : Int)) (duration T j)) :=
  elapsed_replicate (duration T j) (ticks b j)

theorem prefix_elapsed_le_time (b : Nat → Bool) (T : Fraction) (j : Nat)
    (hT : 0 ≤ T.num) :
    Fraction.le (elapsed (List.replicate (ticks b j) (duration T j))) T := by
  let d := duration T j
  have hcount : Fraction.le (Fraction.ofInt (ticks b j : Int))
      (Fraction.ofInt (blocks j : Int)) := by
    unfold Fraction.le Fraction.ofInt
    dsimp
    simp only [Int.mul_one]
    exact Int.ofNat_le.mpr (ticks_le_blocks b j)
  have hm := Fraction.mul_le_mul_nonnegative hcount d hT
  have hfull := endpoint_elapsed T j
  have he := elapsed_replicate d (blocks j)
  have hbound := Fraction.le_equiv_left
    (prefix_elapsed b T j) hm
  exact Fraction.le_equiv_right hbound
    (Fraction.equiv_trans (Fraction.equiv_symm he) hfull)

private theorem schedule_replicate_step (w h : Fraction) (s : Point × Point) :
    (n : Nat) →
      schedule (linearField w) (List.replicate (n + 1) h) s =
        cell (linearField w) h
          (schedule (linearField w) (List.replicate n h) s)
  | 0 => rfl
  | n + 1 => by
      simp only [List.replicate_succ, schedule]
      change schedule (linearField w) (List.replicate (n + 1) h)
        (cell (linearField w) h s) =
          cell (linearField w) h
            (schedule (linearField w) (List.replicate n h)
              (cell (linearField w) h s))
      rw [schedule_replicate_step w h (cell (linearField w) h s) n]

theorem prefix_next (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat) :
    prefixState b w T s (j + 1) =
      if b j then
        cell (linearField w) (duration T (j + 1))
          (fineAt w (duration T (j + 1)) s (ticks b j))
      else fineAt w (duration T (j + 1)) s (ticks b j) := by
  let h := duration T (j + 1)
  by_cases hb : b j
  · simp only [prefixState, ticks_next]
    simp only [bit, hb, ↓reduceIte]
    change schedule (linearField w)
      (List.replicate ((ticks b j + ticks b j) + 1) h) s = _
    rw [schedule_replicate_step]
    rw [← fineDurations_replicate]
    exact congrArg (cell (linearField w) h)
      (fineAt_schedule w h s (ticks b j))
  · simp only [prefixState, ticks_next]
    simp [bit, hb] at *
    rw [← fineDurations_replicate]
    exact fineAt_schedule w h s (ticks b j)

private theorem scalar_one_bound (a b c : Fraction)
    (ha : 0 ≤ a.num) :
    Fraction.le
      (Fraction.add b (Fraction.mul c (Fraction.add a b)))
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) c)
        (Fraction.add a b)) := by
  let M := Fraction.add a b
  have hbM : Fraction.le b M := by
    unfold Fraction.le M Fraction.add
    dsimp
    rw [Int.add_mul]
    have hnon := Int.mul_nonneg
      (Int.mul_nonneg ha (Int.le_of_lt b.den_pos)) (Int.le_of_lt b.den_pos)
    have he : b.num * (a.den * b.den) = b.num * a.den * b.den := by ac_rfl
    rw [he]
    omega
  have hfirst := Fraction.add_le_add_right hbM (Fraction.mul c M)
  apply Fraction.le_equiv_right hfirst
  simp only [Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
  simp only [M, Fraction.add]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

theorem cell_parameter_bound_one (w sigma tau : Fraction) (s : Point × Point)
    (hσ : 0 ≤ sigma.num) (hτ : 0 ≤ tau.num)
    (hsum : Fraction.le (Fraction.add sigma tau) (Fraction.ofInt 1)) :
    Fraction.le
      (stateNorm (stateSub (cell (linearField w) tau s)
        (cell (linearField w) sigma s)))
      (Fraction.mul (durationDifference sigma tau).abs
        (Fraction.mul
          (Fraction.add (Fraction.ofInt 1) w.abs) (stateNorm s))) := by
  let d := durationDifference sigma tau
  have hp := short_sum_point_bound sigma tau s.1 s.2 hσ hτ hsum
  have hw := Fraction.mul_le_mul_nonnegative_left hp w.abs
    (Fraction.abs_num_nonnegative w)
  have ha := Fraction.add_le_add_left hw (pointNorm s.2)
  have hd := Fraction.mul_le_mul_nonnegative_left ha d.abs
    (Fraction.abs_num_nonnegative d)
  have hc := scalar_one_bound (pointNorm s.1) (pointNorm s.2) w.abs
    (pointNorm_nonnegative s.1)
  have hdc := Fraction.mul_le_mul_nonnegative_left hc d.abs
    (Fraction.abs_num_nonnegative d)
  have hf := cell_parameter_norm_formula w sigma tau s
  exact Fraction.le_equiv_right
    (Fraction.magnitudes.le_trans (Fraction.le_equiv_left hf hd) hdc)
    (by simp only [stateNorm]; exact Fraction.equiv_refl _)

private def zero : Fraction := ⟨0, 1, by decide⟩

theorem cell_increment_bound (w h : Fraction) (s : Point × Point)
    (hh : 0 ≤ h.num) (hsmall : Fraction.le h (Fraction.ofInt 1)) :
    Fraction.le (stateNorm (stateSub (cell (linearField w) h s) s))
      (Fraction.mul h.abs
        (Fraction.mul (Fraction.add (Fraction.ofInt 1) w.abs) (stateNorm s))) := by
  have hsum : Fraction.le (Fraction.add zero h) (Fraction.ofInt 1) :=
    Fraction.le_equiv_left (by
      simp only [zero, Fraction.equiv, Fraction.add]
      simp) hsmall
  have hb := cell_parameter_bound_one w zero h s (by decide) hh hsum
  have he : stateEquiv
      (stateSub (cell (linearField w) h s) s)
      (stateSub (cell (linearField w) h s) (cell (linearField w) zero s)) :=
    stateSub_congr
      ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
        ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩
      ⟨⟨Fraction.equiv_symm (zero_step w s).1.1,
          Fraction.equiv_symm (zero_step w s).1.2⟩,
        ⟨Fraction.equiv_symm (zero_step w s).2.1,
          Fraction.equiv_symm (zero_step w s).2.2⟩⟩
  have hfirst := Fraction.le_equiv_left (stateNorm_equiv he) hb
  apply Fraction.le_equiv_right hfirst
  simp only [durationDifference, zero, negF, Fraction.equiv,
    Fraction.abs, Fraction.add, Fraction.mul]
  simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
    Int.natAbs_zero, Int.ofNat_zero, Int.mul_one, Int.one_mul,
    Int.neg_zero]

theorem fine_prefix_state_le_two (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le
      (stateNorm (fineAt w (duration T (j + 1)) s (ticks b j)))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) := by
  let h := duration T (j + 1)
  have hprefix := smallTime_prefix w h (ticks b j) (blocks j) hT
    (ticks_le_blocks b j) (dyadic_smallTime w T j hs)
  exact fine_state_le_two w h s (ticks b j) hT hprefix

theorem prefix_totalTime_le (b : Nat → Bool) (T : Fraction) (j : Nat)
    (hT : 0 ≤ T.num) :
    Fraction.le (totalTime (duration T (j + 1)) (ticks b j)) T := by
  let h := duration T (j + 1)
  have he : Fraction.equiv (totalTime h (ticks b j))
      (elapsed (List.replicate (ticks b j) (duration T j))) :=
    Fraction.equiv_trans
      (Fraction.equiv_symm (coarse_elapsed_totalTime h (ticks b j)))
      (elapsed_replicate_congr
        (Fraction.equiv_symm (duration_halving T j)) (ticks b j))
  exact Fraction.le_equiv_left he (prefix_elapsed_le_time b T j hT)

theorem fine_optional_increment (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le
      (stateNorm (stateSub
        (cell (linearField w) (duration T (j + 1))
          (fineAt w (duration T (j + 1)) s (ticks b j)))
        (fineAt w (duration T (j + 1)) s (ticks b j))))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (duration T (j + 1))
          (Fraction.mul (Fraction.add (Fraction.ofInt 1) w.abs)
            (stateNorm s)))) := by
  let h := duration T (j + 1)
  let q := fineAt w h s (ticks b j)
  have hle : Fraction.le h (Fraction.ofInt 1) := by
    have h₁ := duration_le_time T (j + 1) hT
    have h₂ := dyadic_time_le_half w T hT hs
    have h₃ : Fraction.le (⟨1, 2, by decide⟩ : Fraction)
        (Fraction.ofInt 1) := by unfold Fraction.le; decide
    exact Fraction.magnitudes.le_trans h₁
      (Fraction.magnitudes.le_trans h₂ h₃)
  have hb := cell_increment_bound w h q hT hle
  have hq := fine_prefix_state_le_two b w T s j hT hs
  have hm₁ := Fraction.mul_le_mul_nonnegative_left hq
    (Fraction.add (Fraction.ofInt 1) w.abs) (by
      unfold Fraction.add Fraction.ofInt Fraction.abs
      dsimp
      have hw := Int.ofNat_nonneg w.num.natAbs
      have hd := w.den_pos
      omega)
  have hm₂ := Fraction.mul_le_mul_nonnegative_left hm₁ h hT
  have habs := Fraction.abs_of_nonnegative h hT
  have he := HarmonicDyadic.mul_equiv habs
    (Fraction.equiv_refl
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) w.abs) (stateNorm q)))
  have hchain := Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right hb he) hm₂
  apply Fraction.le_equiv_right hchain
  simp only [h]
  simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
  ac_nf

def refinementCap (w T : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt 3)
    (Fraction.mul T
      (Fraction.mul (duration T (j + 1))
        (Fraction.mul w.abs (stateNorm s))))

def optionalCap (w T : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt 2)
    (Fraction.mul (duration T (j + 1))
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) w.abs)
        (stateNorm s)))

theorem prefix_refinement_error (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le
      (stateNorm (stateSub
        (fineAt w (duration T (j + 1)) s (ticks b j))
        (prefixState b w T s j)))
      (refinementCap w T s j) := by
  let h := duration T (j + 1)
  let n := ticks b j
  have hs' := smallTime_prefix w h n (blocks j) hT
    (ticks_le_blocks b j) (dyadic_smallTime w T j hs)
  have hb := actual_uniform_error w h s n hT hs'
  have he : stateEquiv
      (stateSub (fineAt w h s n) (prefixState b w T s j))
      (stateSub (fineAt w h s n) (coarseAt w h s n)) :=
    stateSub_congr
      ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
        ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩
      (prefix_coarse b w T s j)
  have hfirst := Fraction.le_equiv_left (stateNorm_equiv he) hb
  have htime := prefix_totalTime_le b T j hT
  have hnon : 0 ≤ (Fraction.mul h (Fraction.mul w.abs (stateNorm s))).num :=
    Int.mul_nonneg hT
      (Int.mul_nonneg (Fraction.abs_num_nonnegative w)
        (stateNorm_nonnegative s))
  have hm₁ := Fraction.mul_le_mul_nonnegative htime
    (Fraction.mul h (Fraction.mul w.abs (stateNorm s))) hnon
  have hm₂ := Fraction.mul_le_mul_nonnegative_left hm₁
    (Fraction.ofInt 3) (by decide)
  exact Fraction.magnitudes.le_trans hfirst hm₂

def adjacentCap (w T : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  Fraction.add (optionalCap w T s j) (refinementCap w T s j)

private theorem optionalCap_nonnegative (w T : Fraction) (s : Point × Point)
    (j : Nat) (hT : 0 ≤ T.num) :
    0 ≤ (optionalCap w T s j).num := by
  unfold optionalCap
  have hfactor : 0 ≤ (Fraction.add (Fraction.ofInt 1) w.abs).num := by
    unfold Fraction.add Fraction.ofInt Fraction.abs
    dsimp
    have hw := Int.ofNat_nonneg w.num.natAbs
    have hd := w.den_pos
    omega
  exact Int.mul_nonneg (by decide)
    (Int.mul_nonneg hT
      (Int.mul_nonneg hfactor (stateNorm_nonnegative s)))

private theorem le_add_optional (a c : Fraction) (hc : 0 ≤ c.num) :
    Fraction.le a (Fraction.add c a) := by
  have hz : Fraction.le (Fraction.ofInt 0) c := by
    unfold Fraction.le Fraction.ofInt
    dsimp
    simp only [Int.zero_mul, Int.mul_one]
    exact hc
  have h := Fraction.add_le_add_left hz a
  have he : Fraction.equiv (Fraction.add a (Fraction.ofInt 0)) a := by
    simp only [Fraction.equiv, Fraction.add, Fraction.ofInt]
    simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
      Int.mul_one, Int.one_mul]
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.equiv_symm he) h)
    (Fraction.add_comm a c)

theorem adjacent_error_le_add (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le
      (stateNorm (stateSub (prefixState b w T s (j + 1))
        (prefixState b w T s j)))
      (adjacentCap w T s j) := by
  have hnext := prefix_next b w T s j
  have href := prefix_refinement_error b w T s j hT hs
  by_cases hb : b j
  · rw [hnext, if_pos hb]
    have htri := stateSub_triangle
      (cell (linearField w) (duration T (j + 1))
        (fineAt w (duration T (j + 1)) s (ticks b j)))
      (fineAt w (duration T (j + 1)) s (ticks b j))
      (prefixState b w T s j)
    exact Fraction.magnitudes.le_trans htri
      (Fraction.add_le_add (fine_optional_increment b w T s j hT hs) href)
  · rw [hnext, if_neg hb]
    exact Fraction.magnitudes.le_trans href
      (le_add_optional _ _ (optionalCap_nonnegative w T s j hT))

/-- `A=T*M*(2*(1+|w|)+3*T*|w|)` for intermediate prefixes. -/
def coefficient (w T : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul T
    (Fraction.mul (stateNorm s)
      (Fraction.add
        (Fraction.mul (Fraction.ofInt 2)
          (Fraction.add (Fraction.ofInt 1) w.abs))
        (Fraction.mul (Fraction.ofInt 3) (Fraction.mul T w.abs))))

def tailCap (w T : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  let A := coefficient w T s
  ⟨A.num, A.den * (2 : Int) ^ j,
    Int.mul_pos A.den_pos (Int.pow_pos (by decide))⟩

def doubleTail (w T : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  let A := coefficient w T s
  ⟨2 * A.num, A.den * (2 : Int) ^ j,
    Int.mul_pos A.den_pos (Int.pow_pos (by decide))⟩

theorem adjacentCap_tail (w T : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv (adjacentCap w T s j) (tailCap w T s (j + 1)) := by
  simp only [adjacentCap, optionalCap, refinementCap, tailCap,
    coefficient, duration, Fraction.equiv, Fraction.add,
    Fraction.mul, Fraction.ofInt, Fraction.abs,
    Int.pow_succ]
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
  ac_nf

theorem adjacent_error_le (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le
      (stateNorm (stateSub (prefixState b w T s (j + 1))
        (prefixState b w T s j)))
      (tailCap w T s (j + 1)) :=
  Fraction.le_equiv_right (adjacent_error_le_add b w T s j hT hs)
    (adjacentCap_tail w T s j)

theorem coefficient_nonnegative (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) : 0 ≤ (coefficient w T s).num := by
  have hOneW : 0 ≤ (Fraction.add (Fraction.ofInt 1) w.abs).num := by
    unfold Fraction.add Fraction.ofInt Fraction.abs
    dsimp
    have hw := Int.ofNat_nonneg w.num.natAbs
    have hd := w.den_pos
    omega
  have h₁ : 0 ≤ (Fraction.mul (Fraction.ofInt 2)
      (Fraction.add (Fraction.ofInt 1) w.abs)).num :=
    Int.mul_nonneg (by decide) hOneW
  have h₂ : 0 ≤ (Fraction.mul (Fraction.ofInt 3)
      (Fraction.mul T w.abs)).num :=
    Int.mul_nonneg (by decide)
      (Int.mul_nonneg hT (Fraction.abs_num_nonnegative w))
  unfold coefficient
  exact Int.mul_nonneg hT
    (Int.mul_nonneg (stateNorm_nonnegative s)
      (HarmonicTimeComparison.add_num_nonnegative _ _ h₁ h₂))

theorem tail_halving (w T : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv
      (Fraction.add (tailCap w T s (j + 1)) (tailCap w T s (j + 1)))
      (tailCap w T s j) := by
  simp only [tailCap, Fraction.equiv, Fraction.add, Int.pow_succ]
  simp only [show (2 : Int) = 1 + 1 by rfl, Int.add_mul, Int.mul_add]
  ac_nf

theorem tail_double (w T : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv (Fraction.add (tailCap w T s j) (tailCap w T s j))
      (doubleTail w T s j) := by
  simp only [tailCap, doubleTail, Fraction.equiv, Fraction.add]
  simp only [show (2 : Int) = 1 + 1 by rfl, Int.add_mul, Int.mul_add]
  ac_nf

theorem finite_gap_error (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    (k j : Nat) → Fraction.le
      (stateNorm (stateSub (prefixState b w T s (j + k))
        (prefixState b w T s j))) (tailCap w T s j)
  | 0, j => by
      have hz : Fraction.le (Fraction.ofInt 0) (tailCap w T s j) := by
        simp only [Fraction.le, Fraction.ofInt, tailCap]
        have hc := coefficient_nonnegative w T s hT
        simp only [Int.zero_mul, Int.mul_one]
        exact hc
      simpa only [Nat.add_zero] using
        Fraction.le_equiv_left
          (stateSub_self_norm_zero (prefixState b w T s j)) hz
  | k + 1, j => by
      have htri := stateSub_triangle
        (prefixState b w T s (j + (k + 1)))
        (prefixState b w T s (j + 1)) (prefixState b w T s j)
      have hk : Fraction.le
          (stateNorm (stateSub (prefixState b w T s (j + (k + 1)))
            (prefixState b w T s (j + 1)))) (tailCap w T s (j + 1)) := by
        simpa only [Nat.add_succ, Nat.succ_add, Nat.add_assoc] using
          finite_gap_error b w T s hT hs k (j + 1)
      have ha := adjacent_error_le b w T s j hT hs
      have hsum := Fraction.add_le_add hk ha
      exact Fraction.le_equiv_right (Fraction.magnitudes.le_trans htri hsum)
        (tail_halving w T s j)

theorem two_sided_error (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (N m n : Nat) (hm : N ≤ m) (hn : N ≤ n) :
    Fraction.le
      (stateNorm (stateSub (prefixState b w T s m) (prefixState b w T s n)))
      (doubleTail w T s N) := by
  have hm' : N + (m - N) = m := by omega
  have hn' : N + (n - N) = n := by omega
  have hfirst := finite_gap_error b w T s hT hs (m - N) N
  have hsecond := finite_gap_error b w T s hT hs (n - N) N
  rw [hm'] at hfirst
  rw [hn'] at hsecond
  have hsecond' := Fraction.le_equiv_left
    (stateSub_norm_symm (prefixState b w T s N) (prefixState b w T s n)) hsecond
  have htri := stateSub_triangle
    (prefixState b w T s m) (prefixState b w T s N) (prefixState b w T s n)
  exact Fraction.le_equiv_right
    (Fraction.magnitudes.le_trans htri (Fraction.add_le_add hfirst hsecond'))
    (tail_double w T s N)

def modulus (w T : Fraction) (s : Point × Point) (eps : Fraction) : Nat :=
  (2 * (coefficient w T s).num * eps.den).toNat

theorem doubleTail_lt_tolerance (w T : Fraction) (s : Point × Point)
    (eps : Fraction) (hT : 0 ≤ T.num) (heps : 0 < eps.num) :
    Fraction.lt (doubleTail w T s (modulus w T s eps)) eps := by
  let A := coefficient w T s
  let N := modulus w T s eps
  have hA : 0 ≤ A.num := coefficient_nonnegative w T s hT
  have hL : 0 ≤ 2 * A.num * eps.den :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) hA) (Int.le_of_lt eps.den_pos)
  have hN : (N : Int) = 2 * A.num * eps.den :=
    Int.toNat_of_nonneg hL
  have hpow := two_pow_ge_succ N
  have hp : 0 ≤ (2 : Int) ^ N := Int.le_of_lt (Int.pow_pos (by decide))
  have hfactor : 1 ≤ eps.num * A.den := by
    have hmul := Int.mul_pos heps A.den_pos
    omega
  have hmult := Int.mul_le_mul_of_nonneg_right hfactor hp
  simp only [Int.one_mul] at hmult
  unfold Fraction.lt doubleTail
  dsimp
  change 2 * A.num * eps.den < eps.num * (A.den * (2 : Int) ^ N)
  rw [← Int.mul_assoc]
  omega

theorem prefix_cauchy (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    ∀ eps : Fraction, 0 < eps.num →
      ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
        Fraction.lt
          (stateNorm (stateSub (prefixState b w T s m)
            (prefixState b w T s n))) eps := by
  intro eps heps
  refine ⟨modulus w T s eps, ?_⟩
  intro m n hm hn
  exact Fraction.magnitudes.lt_of_le_lt
    (two_sided_error b w T s hT hs _ m n hm hn)
    (doubleTail_lt_tolerance w T s eps hT heps)

def prefixName (b : Nat → Bool) (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) : EndpointCauchyName where
  approx := prefixState b w T s
  cauchy := prefix_cauchy b w T s hT hs

theorem all_zero_ticks (j : Nat) : ticks (fun _ => false) j = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [ticks, bit, ih]

theorem all_zero_prefix (w T : Fraction) (s : Point × Point) (j : Nat) :
    prefixState (fun _ => false) w T s j = s := by
  simp [prefixState, all_zero_ticks, schedule]

theorem zero_time_prefix (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat) (hT : T.num = 0) :
    stateEquiv (prefixState b w T s j) s := by
  exact zero_duration_schedule w (duration T j) (by exact hT) (ticks b j) s

private def sampleOne : Fraction := ⟨1, 1, by decide⟩
private def sampleZero : Fraction := ⟨0, 1, by decide⟩
private def sampleQuarter : Fraction := ⟨1, 4, by decide⟩
private def sampleState : Point × Point :=
  ((sampleOne, sampleZero), (sampleZero, sampleOne))
private def firstBit (j : Nat) : Bool := j == 0

theorem sample_ticks : ticks firstBit 1 = 1 ∧ ticks firstBit 2 = 2 := by decide

theorem sample_first_error :
    Fraction.equiv
      (stateNorm (stateSub
        (prefixState firstBit sampleOne sampleQuarter sampleState 1)
        (prefixState firstBit sampleOne sampleQuarter sampleState 0)))
      ⟨17, 64, by decide⟩ := by decide

theorem sample_coefficient :
    Fraction.equiv (coefficient sampleOne sampleQuarter sampleState)
      ⟨19, 8, by decide⟩ := by decide

theorem sample_second_error :
    Fraction.equiv
      (stateNorm (stateSub
        (prefixState firstBit sampleOne sampleQuarter sampleState 2)
        (prefixState firstBit sampleOne sampleQuarter sampleState 1)))
      ⟨545, 65536, by decide⟩ := by decide

def sample_prefix_cauchy_name : EndpointCauchyName :=
  prefixName firstBit sampleOne sampleQuarter sampleState
    (by decide) (by unfold DyadicSmallTime Fraction.le; decide)

end NewtonLimitDynamics.Polygon.HarmonicBinaryPrefix
