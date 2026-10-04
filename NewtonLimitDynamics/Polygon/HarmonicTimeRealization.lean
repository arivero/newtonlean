import NewtonLimitDynamics.Polygon.BinaryTime

/-!
Actual harmonic state values indexed by the constructed binary-time quotient.
All comparisons use finite same-grid end-kick schedules. The quotient is not
identified with an external real interval; force identification and actual
intervening-region area remain separate.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicTimeRealization

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicComparison
open HarmonicAccumulation
open HarmonicUniform
open HarmonicDyadic
open HarmonicBinaryPrefix
open HarmonicTimeComparison
open PointBounds
open CauchyValues
open BinaryTime

def countState (w T : Fraction) (s : Point × Point)
    (j n : Nat) : Point × Point :=
  schedule (linearField w) (List.replicate n (duration T j)) s

theorem countState_coarse (w T : Fraction) (s : Point × Point)
    (j n : Nat) :
    stateEquiv (countState w T s j n)
      (coarseAt w (duration T (j + 1)) s n) := by
  let h := duration T (j + 1)
  have hc := schedule_replicate_congr w (duration T j) (Fraction.add h h)
    (duration_halving T j) n s s
    ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩
  simpa only [countState, coarseAt_schedule] using hc

theorem countState_le_two (w T : Fraction) (s : Point × Point)
    (j n : Nat) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hn : n ≤ blocks j) :
    Fraction.le (stateNorm (countState w T s j n))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) := by
  let h := duration T (j + 1)
  have hprefix := smallTime_prefix w h n (blocks j) hT hn
    (dyadic_smallTime w T j hs)
  exact Fraction.le_equiv_left (stateNorm_equiv (countState_coarse w T s j n))
    (coarse_state_le_two w h s n hT hprefix)

def stateTimeFactor (w : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul (Fraction.ofInt 2)
    (Fraction.mul (Fraction.add (Fraction.ofInt 1) w.abs) (stateNorm s))

theorem countState_step_bound (w T : Fraction) (s : Point × Point)
    (j n : Nat) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hn : n ≤ blocks j) :
    Fraction.le (distance (countState w T s j (n + 1))
      (countState w T s j n))
      (Fraction.mul (duration T j) (stateTimeFactor w s)) := by
  let h := duration T j
  let q := countState w T s j n
  have hle : Fraction.le h (Fraction.ofInt 1) := by
    have h₁ := duration_le_time T j hT
    have h₂ := dyadic_time_le_half w T hT hs
    have h₃ : Fraction.le (⟨1, 2, by decide⟩ : Fraction)
        (Fraction.ofInt 1) := by unfold Fraction.le; decide
    exact Fraction.magnitudes.le_trans h₁
      (Fraction.magnitudes.le_trans h₂ h₃)
  have hb := cell_increment_bound w h q hT hle
  have hq := countState_le_two w T s j n hT hs hn
  have hfac : 0 ≤ (Fraction.add (Fraction.ofInt 1) w.abs).num := by
    unfold Fraction.add Fraction.ofInt Fraction.abs
    dsimp
    have hw := Int.ofNat_nonneg w.num.natAbs
    have hd := w.den_pos
    omega
  have hm₁ := Fraction.mul_le_mul_nonnegative_left hq
    (Fraction.add (Fraction.ofInt 1) w.abs) hfac
  have hm₂ := Fraction.mul_le_mul_nonnegative_left hm₁ h hT
  have habs := Fraction.abs_of_nonnegative h hT
  have he := HarmonicDyadic.mul_equiv habs
    (Fraction.equiv_refl
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) w.abs) (stateNorm q)))
  have hchain := Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right hb he) hm₂
  have hstep : countState w T s j (n + 1) = cell (linearField w) h q :=
    schedule_replicate_step w h s n
  rw [hstep]
  change Fraction.le (stateNorm (stateSub (cell (linearField w) h q) q))
    (Fraction.mul h (stateTimeFactor w s))
  apply Fraction.le_equiv_right hchain
  simp only [stateTimeFactor, Fraction.equiv, Fraction.mul, Fraction.ofInt]
  ac_nf

theorem countState_gap (w T : Fraction) (s : Point × Point)
    (j : Nat) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    (n k : Nat) → n + k ≤ blocks j →
      Fraction.le (distance (countState w T s j (n + k))
        (countState w T s j n))
        (Fraction.mul (Fraction.ofInt (k : Int))
          (Fraction.mul (duration T j) (stateTimeFactor w s)))
  | n, 0, _ => by
      have hz := stateSub_self_norm_zero (countState w T s j n)
      apply Fraction.le_of_equiv
      apply Fraction.equiv_trans hz
      simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp
  | n, k + 1, hnk => by
      have hk : n + k ≤ blocks j := by omega
      have htri := stateSub_triangle
        (countState w T s j (n + (k + 1)))
        (countState w T s j (n + k)) (countState w T s j n)
      have hstep : Fraction.le
          (distance (countState w T s j (n + (k + 1)))
            (countState w T s j (n + k)))
          (Fraction.mul (duration T j) (stateTimeFactor w s)) := by
        simpa only [Nat.add_succ] using
          countState_step_bound w T s j (n + k) hT hs hk
      have hprev := countState_gap w T s j hT hs n k hk
      have hsum := Fraction.add_le_add hstep hprev
      apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans htri hsum)
      simp only [Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
        Int.natCast_add, Int.natCast_one]
      simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
      ac_nf

def countTime (T : Fraction) (j n : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt (n : Int)) (duration T j)

theorem countTime_difference (T : Fraction) (j n k : Nat) :
    Fraction.equiv
      (durationDifference (countTime T j n) (countTime T j (n + k)))
      (Fraction.mul (Fraction.ofInt (k : Int)) (duration T j)) := by
  simp only [countTime, durationDifference, negF, Fraction.equiv,
    Fraction.add, Fraction.mul, Fraction.ofInt, Int.natCast_add]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.one_mul, Int.mul_one]
  ac_nf <;> omega

theorem countTime_abs_difference (T : Fraction) (j n k : Nat)
    (hT : 0 ≤ T.num) :
    Fraction.equiv
      (durationDifference (countTime T j n) (countTime T j (n + k))).abs
      (Fraction.mul (Fraction.ofInt (k : Int)) (duration T j)) := by
  have hs := Fraction.abs_equiv (countTime_difference T j n k)
  have hnon : 0 ≤ (Fraction.mul (Fraction.ofInt (k : Int)) (duration T j)).num :=
    Int.mul_nonneg (Int.ofNat_nonneg _) hT
  exact Fraction.equiv_trans hs
    (Fraction.abs_of_nonnegative _ hnon)

theorem stateTimeFactor_nonnegative (w : Fraction) (s : Point × Point) :
    0 ≤ (stateTimeFactor w s).num := by
  unfold stateTimeFactor Fraction.mul Fraction.add Fraction.ofInt Fraction.abs
  dsimp
  have hw := Int.ofNat_nonneg w.num.natAbs
  have hd := w.den_pos
  have hm := stateNorm_nonnegative s
  exact Int.mul_nonneg (by decide)
    (Int.mul_nonneg (by omega) hm)

theorem countState_ordered_bound (w T : Fraction) (s : Point × Point)
    (j n k : Nat) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hnk : n + k ≤ blocks j) :
    Fraction.le (distance (countState w T s j (n + k))
      (countState w T s j n))
      (Fraction.mul
        (durationDifference (countTime T j n) (countTime T j (n + k))).abs
        (stateTimeFactor w s)) := by
  have hb := countState_gap w T s j hT hs n k hnk
  apply Fraction.le_equiv_right hb
  have he := countTime_abs_difference T j n k hT
  apply Fraction.equiv_symm
  apply Fraction.equiv_trans
    (HarmonicDyadic.mul_equiv he (Fraction.equiv_refl _))
  simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
  ac_nf

theorem durationDifference_abs_symm (a b : Fraction) :
    Fraction.equiv (durationDifference a b).abs
      (durationDifference b a).abs := by
  have he : Fraction.equiv (durationDifference a b)
      (negF (durationDifference b a)) := by
    simp only [durationDifference, negF, Fraction.equiv,
      Fraction.add]
    simp only [Int.mul_add, Int.mul_neg, Int.neg_mul, Int.neg_add,
      Int.neg_neg]
    ac_nf <;> omega
  exact Fraction.equiv_trans (Fraction.abs_equiv he)
    (Fraction.abs_neg _)

theorem countState_same_grid_bound (w T : Fraction) (s : Point × Point)
    (j m n : Nat) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hm : m ≤ blocks j) (hn : n ≤ blocks j) :
    Fraction.le (distance (countState w T s j m)
      (countState w T s j n))
      (Fraction.mul
        (durationDifference (countTime T j n) (countTime T j m)).abs
        (stateTimeFactor w s)) := by
  rcases Nat.le_total n m with hnm | hmn
  · have he : n + (m - n) = m := by omega
    have hb := countState_ordered_bound w T s j n (m - n) hT hs
      (by simpa only [he] using hm)
    simpa only [he] using hb
  · have he : m + (n - m) = n := by omega
    have hb := countState_ordered_bound w T s j m (n - m) hT hs
      (by simpa only [he] using hn)
    rw [he] at hb
    have hd := stateSub_norm_symm (countState w T s j m)
      (countState w T s j n)
    have ht := durationDifference_abs_symm (countTime T j m)
      (countTime T j n)
    exact Fraction.le_equiv_right
      (Fraction.le_equiv_left hd hb)
      (HarmonicDyadic.mul_equiv ht (Fraction.equiv_refl _))

theorem prefix_time_bound (b c : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (j : Nat) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) :
    Fraction.le (distance (prefixState b w T s j)
      (prefixState c w T s j))
      (Fraction.mul (distance (timeState b T j) (timeState c T j))
        (stateTimeFactor w s)) := by
  have hb := countState_same_grid_bound w T s j (ticks b j) (ticks c j)
    hT hs (ticks_le_blocks b j) (ticks_le_blocks c j)
  apply Fraction.le_equiv_right hb
  exact HarmonicDyadic.mul_equiv
    (Fraction.equiv_symm (scalarState_distance
      (timeApprox b T j) (timeApprox c T j)))
    (Fraction.equiv_refl _)

def factorDenominator (C : Fraction) : Fraction :=
  Fraction.add C (Fraction.ofInt 1)

theorem factorDenominator_positive (C : Fraction) (hC : 0 ≤ C.num) :
    0 < (factorDenominator C).num := by
  unfold factorDenominator Fraction.add Fraction.ofInt
  dsimp
  have hd := C.den_pos
  omega

def factorDelta (C eps : Fraction) (hC : 0 ≤ C.num) : Fraction :=
  ⟨eps.num * (factorDenominator C).den,
    eps.den * (factorDenominator C).num,
    Int.mul_pos eps.den_pos
      (factorDenominator_positive C hC)⟩

theorem factorDelta_positive (C eps : Fraction) (hC : 0 ≤ C.num)
    (heps : 0 < eps.num) : 0 < (factorDelta C eps hC).num :=
  Int.mul_pos heps (factorDenominator C).den_pos

theorem factor_control (C eps d : Fraction) (hC : 0 ≤ C.num)
    (hd : 0 ≤ d.num)
    (hdelta : Fraction.lt d (factorDelta C eps hC)) :
    Fraction.lt (Fraction.mul d C) eps := by
  have hden : Fraction.le C (factorDenominator C) := by
    unfold factorDenominator Fraction.le Fraction.add Fraction.ofInt
    dsimp
    have hp := C.den_pos
    have hsq : 0 ≤ C.den * C.den :=
      Int.mul_nonneg (Int.le_of_lt hp) (Int.le_of_lt hp)
    simp only [Int.one_mul, Int.mul_one, Int.add_mul]
    omega
  have hweak := Fraction.mul_le_mul_nonnegative_left hden d hd
  have hstrict : Fraction.lt
      (Fraction.mul d (factorDenominator C))
      (Fraction.mul (factorDelta C eps hC) (factorDenominator C)) := by
    have hm := Int.mul_lt_mul_of_pos_right hdelta
      (Int.mul_pos (factorDenominator_positive C hC)
        (factorDenominator C).den_pos)
    unfold Fraction.lt Fraction.mul at *
    dsimp at *
    have h₁ : d.num * (factorDenominator C).num *
        ((factorDelta C eps hC).den * (factorDenominator C).den) =
        (d.num * (factorDelta C eps hC).den) *
          ((factorDenominator C).num * (factorDenominator C).den) := by ac_rfl
    have h₂ : (factorDelta C eps hC).num *
        (factorDenominator C).num *
        (d.den * (factorDenominator C).den) =
        ((factorDelta C eps hC).num * d.den) *
          ((factorDenominator C).num * (factorDenominator C).den) := by ac_rfl
    rw [h₁, h₂]
    exact hm
  have hproduct : Fraction.equiv
      (Fraction.mul (factorDelta C eps hC) (factorDenominator C)) eps := by
    unfold Fraction.equiv Fraction.mul factorDelta
    dsimp
    ac_nf
  exact Fraction.magnitudes.lt_of_lt_le
    (Fraction.magnitudes.lt_of_le_lt hweak hstrict)
    ((Fraction.equiv_iff_mutual_le _ _).mp hproduct).1

theorem factor_delta_weak (C eps : Fraction) (hC : 0 ≤ C.num)
    (heps : 0 ≤ eps.num) :
    Fraction.le (Fraction.mul (factorDelta C eps hC) C) eps := by
  have hden : Fraction.le C (factorDenominator C) := by
    unfold factorDenominator Fraction.le Fraction.add Fraction.ofInt
    dsimp
    have hp := C.den_pos
    have hsq : 0 ≤ C.den * C.den :=
      Int.mul_nonneg (Int.le_of_lt hp) (Int.le_of_lt hp)
    simp only [Int.one_mul, Int.mul_one, Int.add_mul]
    omega
  have hm := Fraction.mul_le_mul_nonnegative_left hden
    (factorDelta C eps hC)
    (by
      unfold factorDelta
      dsimp
      exact Int.mul_nonneg heps
        (Int.le_of_lt (factorDenominator C).den_pos))
  apply Fraction.le_equiv_right hm
  unfold Fraction.equiv Fraction.mul factorDelta
  dsimp
  ac_nf

theorem mul_add_equiv (a b c : Fraction) :
    Fraction.equiv (Fraction.mul (Fraction.add a b) c)
      (Fraction.add (Fraction.mul a c) (Fraction.mul b c)) := by
  simp only [Fraction.equiv, Fraction.mul, Fraction.add]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

theorem nameBound_scale (a b ta tb : EndpointCauchyName)
    (C R : Fraction) (hC : 0 ≤ C.num)
    (hlevel : ∀ n : Nat,
      Fraction.le (distance (a.approx n) (b.approx n))
        (Fraction.mul (distance (ta.approx n) (tb.approx n)) C))
    (hnear : NameBound ta tb R) :
    NameBound a b (Fraction.mul R C) := by
  intro eps heps
  let q := eps.half
  let delta := factorDelta C q hC
  obtain ⟨N, hN⟩ := hnear delta
    (factorDelta_positive C q hC heps)
  refine ⟨N, ?_⟩
  intro n hn
  have hmul := Fraction.mul_le_mul_nonnegative
    (Fraction.magnitudes.lt_implies_le (hN n hn)) C hC
  have hsum := Fraction.le_equiv_right hmul (mul_add_equiv R delta C)
  have hdelta := factor_delta_weak C q hC
    (by simpa only [q, Fraction.half] using Int.le_of_lt heps)
  have htotal := Fraction.add_le_add_left hdelta (Fraction.mul R C)
  have hsmall : Fraction.lt
      (Fraction.add (Fraction.mul R C) q)
      (Fraction.add (Fraction.mul R C) eps) :=
    CauchyValues.add_lt_add_left (Fraction.half_lt eps heps) _
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.magnitudes.le_trans (hlevel n)
      (Fraction.magnitudes.le_trans hsum htotal)) hsmall

theorem address_state_equiv (b c : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T)
    (hbc : AddressEquiv T hT b c) :
    NameEquiv (prefixName b w T s hT hs)
      (prefixName c w T s hT hs) := by
  intro eps heps
  let C := stateTimeFactor w s
  have hC := stateTimeFactor_nonnegative w s
  let delta := factorDelta C eps hC
  obtain ⟨N, hN⟩ := hbc delta (factorDelta_positive C eps hC heps)
  refine ⟨N, ?_⟩
  intro j hj
  have hb := prefix_time_bound b c w T s j hT hs
  have hsmall := factor_control C eps
    (distance (timeState b T j) (timeState c T j)) hC
    (stateNorm_nonnegative _) (hN j hj)
  exact Fraction.magnitudes.lt_of_le_lt hb hsmall

def gammaValue (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    BinaryTime T hT → Value :=
  Quotient.lift
    (fun b => binaryValue b w T s hT hs)
    (fun b c hbc => Quotient.sound
      (address_state_equiv b c w T s hT hs hbc))

theorem gammaValue_address (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) :
    gammaValue w T s hT hs (Quotient.mk _ b) =
      binaryValue b w T s hT hs := rfl

def timeCoordinate (T : Fraction) (hT : 0 ≤ T.num) :
    BinaryTime T hT → Value :=
  Quotient.lift (fun b => BinaryTime.timeValue b T hT)
    (fun _ _ h => Quotient.sound h)

theorem timeCoordinate_injective (T : Fraction) (hT : 0 ≤ T.num) :
    ∀ x y : BinaryTime T hT,
      timeCoordinate T hT x = timeCoordinate T hT y → x = y := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ b =>
    induction y using Quotient.inductionOn with
    | _ c =>
      change BinaryTime.timeValue b T hT =
        BinaryTime.timeValue c T hT at hxy
      have hnames : NameEquiv (BinaryTime.timeName b T hT)
          (BinaryTime.timeName c T hT) := Quotient.exact hxy
      exact Quotient.sound hnames

def TimeWithin (T : Fraction) (hT : 0 ≤ T.num)
    (x y : BinaryTime T hT) (R : Fraction) : Prop :=
  Within (timeCoordinate T hT x) (timeCoordinate T hT y) R

theorem timeWithin_address (b c : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) (R : Fraction) :
    TimeWithin T hT (Quotient.mk _ b) (Quotient.mk _ c) R ↔
      NameBound (BinaryTime.timeName b T hT)
        (BinaryTime.timeName c T hT) R := Iff.rfl

theorem gamma_within (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (x y : BinaryTime T hT) (R : Fraction)
    (_hR : 0 ≤ R.num) (hxy : TimeWithin T hT x y R) :
    Within (gammaValue w T s hT hs x)
      (gammaValue w T s hT hs y)
      (Fraction.mul R (stateTimeFactor w s)) := by
  induction x using Quotient.inductionOn with
  | _ b =>
    induction y using Quotient.inductionOn with
    | _ c =>
      change NameBound (BinaryTime.timeName b T hT)
        (BinaryTime.timeName c T hT) R at hxy
      change NameBound (prefixName b w T s hT hs)
        (prefixName c w T s hT hs)
        (Fraction.mul R (stateTimeFactor w s))
      apply nameBound_scale (prefixName b w T s hT hs)
        (prefixName c w T s hT hs)
        (BinaryTime.timeName b T hT) (BinaryTime.timeName c T hT)
        (stateTimeFactor w s) R (stateTimeFactor_nonnegative w s)
      · intro j
        exact prefix_time_bound b c w T s j hT hs
      · exact hxy

theorem nameBound_mono (a b : EndpointCauchyName) (R S : Fraction)
    (hRS : Fraction.le R S) (h : NameBound a b R) :
    NameBound a b S := by
  intro eps heps
  obtain ⟨N, hN⟩ := h eps heps
  refine ⟨N, ?_⟩
  intro n hn
  exact Fraction.magnitudes.lt_of_lt_le (hN n hn)
    (Fraction.add_le_add_right hRS eps)

theorem within_mono (x y : Value) (R S : Fraction)
    (hRS : Fraction.le R S) (h : Within x y R) : Within x y S := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact nameBound_mono a b R S hRS h

def timeTolerance (w : Fraction) (s : Point × Point)
    (eps : Fraction) : Fraction :=
  factorDelta (stateTimeFactor w s) eps.half
    (stateTimeFactor_nonnegative w s)

theorem timeTolerance_positive (w : Fraction) (s : Point × Point)
    (eps : Fraction) (heps : 0 < eps.num) :
    0 < (timeTolerance w s eps).num :=
  factorDelta_positive _ _ _ heps

theorem gamma_uniform_continuity (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (eps : Fraction) (heps : 0 < eps.num)
    (x y : BinaryTime T hT)
    (hxy : TimeWithin T hT x y (timeTolerance w s eps)) :
    Within (gammaValue w T s hT hs x)
      (gammaValue w T s hT hs y) eps.half := by
  have hb := gamma_within w T s hT hs x y
    (timeTolerance w s eps)
    (Int.le_of_lt (timeTolerance_positive w s eps heps)) hxy
  exact within_mono _ _ _ _
    (factor_delta_weak _ _ (stateTimeFactor_nonnegative w s)
      (by simpa only [Fraction.half] using Int.le_of_lt heps)) hb

theorem duration_eventually_small (T eps : Fraction)
    (hT : 0 ≤ T.num) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j : Nat, N ≤ j →
      Fraction.lt (duration T j) eps := by
  let N := (T.num * eps.den).toNat
  have hL : 0 ≤ T.num * eps.den :=
    Int.mul_nonneg hT (Int.le_of_lt eps.den_pos)
  have hN : (N : Int) = T.num * eps.den := Int.toNat_of_nonneg hL
  refine ⟨N, ?_⟩
  intro j hj
  have hpow := two_pow_ge_succ j
  have hp : 0 ≤ (2 : Int) ^ j := Int.le_of_lt (Int.pow_pos (by decide))
  have hfactor : 1 ≤ eps.num * T.den := by
    have hmul := Int.mul_pos heps T.den_pos
    omega
  have hmult := Int.mul_le_mul_of_nonneg_right hfactor hp
  simp only [Int.one_mul] at hmult
  unfold Fraction.lt duration
  dsimp
  change T.num * eps.den < eps.num * (T.den * (2 : Int) ^ j)
  rw [← Int.mul_assoc]
  omega

theorem duration_factor_eventually_small (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j : Nat, N ≤ j →
      Fraction.lt (Fraction.mul (duration T j) (stateTimeFactor w s))
        eps := by
  let C := stateTimeFactor w s
  let delta := factorDelta C eps (stateTimeFactor_nonnegative w s)
  obtain ⟨N, hN⟩ := duration_eventually_small T delta hT
    (factorDelta_positive C eps (stateTimeFactor_nonnegative w s) heps)
  refine ⟨N, ?_⟩
  intro j hj
  exact factor_control C eps (duration T j)
    (stateTimeFactor_nonnegative w s) hT (hN j hj)

def leftAddress : Nat → Bool := fun _ => false
def rightAddress : Nat → Bool := fun _ => true

def leftTime (T : Fraction) (hT : 0 ≤ T.num) : BinaryTime T hT :=
  Quotient.mk _ leftAddress
def rightTime (T : Fraction) (hT : 0 ≤ T.num) : BinaryTime T hT :=
  Quotient.mk _ rightAddress

theorem left_time_state_equiv (T : Fraction) (j : Nat) :
    stateEquiv (timeState leftAddress T j)
      (scalarState (Fraction.ofInt 0)) := by
  have ht : Fraction.equiv (timeApprox leftAddress T j)
      (Fraction.ofInt 0) := by
    have hz : ticks leftAddress j = 0 :=
      all_zero_ticks j
    simp only [timeApprox, hz, Fraction.equiv, Fraction.mul,
      Fraction.ofInt]
    simp
  exact ⟨⟨ht, Fraction.equiv_refl _⟩,
    ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩

theorem left_time_coordinate (T : Fraction) (hT : 0 ≤ T.num) :
    timeCoordinate T hT (leftTime T hT) =
      embed (scalarState (Fraction.ofInt 0)) := by
  apply Quotient.sound
  intro eps heps
  refine ⟨0, ?_⟩
  intro j _
  have he := (distance_zero_iff_stateEquiv
    (timeState leftAddress T j)
    (scalarState (Fraction.ofInt 0))).mpr
      (left_time_state_equiv T j)
  have hself := stateSub_self_norm_zero
    (scalarState (Fraction.ofInt 0))
  have hle : Fraction.le
      (distance (timeState leftAddress T j)
        (scalarState (Fraction.ofInt 0)))
      (distance (scalarState (Fraction.ofInt 0))
        (scalarState (Fraction.ofInt 0))) := Fraction.le_of_equiv
    (Fraction.equiv_trans he (Fraction.equiv_symm hself))
  exact Fraction.magnitudes.lt_of_le_lt hle
    (distance_self_lt _ eps heps)

theorem left_endpoint_value (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    gammaValue w T s hT hs (leftTime T hT) = embed s := by
  apply Quotient.sound
  intro eps heps
  refine ⟨0, ?_⟩
  intro j _
  change Fraction.lt (distance (prefixState leftAddress w T s j) s) eps
  rw [show prefixState leftAddress w T s j = s from
    all_zero_prefix w T s j]
  exact distance_self_lt s eps heps

theorem right_ticks (j : Nat) : ticks rightAddress j + 1 = blocks j := by
  induction j with
  | zero => simp [ticks, rightAddress, bit, blocks]
  | succ j ih =>
      rw [ticks, blocks_succ]
      simp only [rightAddress, bit, ite_true]
      omega

theorem right_time_difference (T : Fraction) (j : Nat) :
    Fraction.equiv (durationDifference (timeApprox rightAddress T j) T)
      (duration T j) := by
  have hk : (ticks rightAddress j : Int) + 1 = (2 : Int) ^ j := by
    have hr := right_ticks j
    have hr' := congrArg Int.ofNat hr
    change ((ticks rightAddress j + 1 : Nat) : Int) =
      ((2 ^ j : Nat) : Int) at hr'
    rw [Int.natCast_add, Int.natCast_one, Int.natCast_pow] at hr'
    exact hr'
  simp only [timeApprox, durationDifference, negF, Fraction.equiv,
    Fraction.add, Fraction.mul, Fraction.ofInt, duration]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  rw [← hk]
  simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
  ac_nf <;> omega

theorem right_time_distance (T : Fraction) (j : Nat)
    (hT : 0 ≤ T.num) :
    Fraction.equiv (distance (timeState rightAddress T j)
      (scalarState T)) (duration T j) := by
  have h₁ := scalarState_distance (timeApprox rightAddress T j) T
  have h₂ := durationDifference_abs_symm T (timeApprox rightAddress T j)
  have h₃ := Fraction.abs_equiv (right_time_difference T j)
  have h₄ := Fraction.abs_of_nonnegative (duration T j) hT
  exact Fraction.equiv_trans h₁
    (Fraction.equiv_trans h₂ (Fraction.equiv_trans h₃ h₄))

theorem right_time_coordinate (T : Fraction) (hT : 0 ≤ T.num) :
    timeCoordinate T hT (rightTime T hT) = embed (scalarState T) := by
  apply Quotient.sound
  intro eps heps
  obtain ⟨N, hN⟩ := duration_eventually_small T eps hT heps
  refine ⟨N, ?_⟩
  intro j hj
  exact Fraction.magnitudes.lt_of_le_lt
    ((Fraction.equiv_iff_mutual_le _ _).mp
      (right_time_distance T j hT)).1 (hN j hj)

theorem right_prefix_endpoint_bound (w T : Fraction)
    (s : Point × Point) (j : Nat) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) :
    Fraction.le (distance (endpoint w T s j)
      (prefixState rightAddress w T s j))
      (Fraction.mul (duration T j) (stateTimeFactor w s)) := by
  have hcount : ticks rightAddress j + 1 ≤ blocks j :=
    Nat.le_of_eq (right_ticks j)
  have hb := countState_gap w T s j hT hs (ticks rightAddress j) 1 hcount
  rw [right_ticks] at hb
  change Fraction.le (distance (endpoint w T s j)
    (prefixState rightAddress w T s j)) _ at hb
  apply Fraction.le_equiv_right hb
  simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt,
    Int.natCast_one,
    Int.one_mul, Int.mul_one]

theorem right_endpoint_value (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    gammaValue w T s hT hs (rightTime T hT) =
      endpointValue w T s hT hs := by
  apply Quotient.sound
  intro eps heps
  obtain ⟨N, hN⟩ := duration_factor_eventually_small w T s hT eps heps
  refine ⟨N, ?_⟩
  intro j hj
  have hb := right_prefix_endpoint_bound w T s j hT hs
  have hs := stateSub_norm_symm
    (prefixState rightAddress w T s j) (endpoint w T s j)
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_equiv_left hs hb) (hN j hj)

def firstAlias (j : Nat) : Bool := decide (j = 0)
def secondAlias (j : Nat) : Bool := decide (j ≠ 0)

theorem alias_ticks (j : Nat) :
    ticks firstAlias (j + 1) = blocks j ∧
      ticks secondAlias (j + 1) + 1 = blocks j := by
  induction j with
  | zero =>
      constructor <;> decide
  | succ j ih =>
      rcases ih with ⟨hfirst, hsecond⟩
      constructor
      · change 2 * ticks firstAlias (j + 1) + bit firstAlias (j + 1) =
          blocks (j + 1)
        have hb : bit firstAlias (j + 1) = 0 := by
          simp [bit, firstAlias]
        rw [hb, blocks_succ]
        omega
      · change 2 * ticks secondAlias (j + 1) +
          bit secondAlias (j + 1) + 1 = blocks (j + 1)
        have hb : bit secondAlias (j + 1) = 1 := by
          simp [bit, secondAlias]
        rw [hb, blocks_succ]
        omega

theorem alias_time_distance (T : Fraction) (j : Nat)
    (hT : 0 ≤ T.num) :
    Fraction.equiv
      (distance (timeState firstAlias T (j + 1))
        (timeState secondAlias T (j + 1)))
      (duration T (j + 1)) := by
  have hcounts : ticks secondAlias (j + 1) + 1 =
      ticks firstAlias (j + 1) := by
    have ha := alias_ticks j
    omega
  have htime := countTime_abs_difference T (j + 1)
    (ticks secondAlias (j + 1)) 1 hT
  rw [hcounts] at htime
  have hd := scalarState_distance
    (timeApprox firstAlias T (j + 1))
    (timeApprox secondAlias T (j + 1))
  apply Fraction.equiv_trans hd
  apply Fraction.equiv_trans htime
  simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt,
    Int.natCast_one, Int.one_mul, Int.mul_one]

theorem alias_address_equiv (T : Fraction) (hT : 0 ≤ T.num) :
    AddressEquiv T hT firstAlias secondAlias := by
  intro eps heps
  obtain ⟨N, hN⟩ := duration_eventually_small T eps hT heps
  refine ⟨N + 1, ?_⟩
  intro j hj
  have hj' : j - 1 + 1 = j := by omega
  have hbound := alias_time_distance T (j - 1) hT
  rw [hj'] at hbound
  exact Fraction.magnitudes.lt_of_le_lt
    ((Fraction.equiv_iff_mutual_le _ _).mp hbound).1
    (hN j (by omega))

theorem alias_time_eq (T : Fraction) (hT : 0 ≤ T.num) :
    (Quotient.mk (addressSetoid T hT) firstAlias : BinaryTime T hT) =
      Quotient.mk (addressSetoid T hT) secondAlias :=
  Quotient.sound (alias_address_equiv T hT)

theorem alias_value_eq (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    binaryValue firstAlias w T s hT hs =
      binaryValue secondAlias w T s hT hs := by
  exact congrArg (gammaValue w T s hT hs) (alias_time_eq T hT)

theorem zero_time_value (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (hzero : T.num = 0) :
    gammaValue w T s hT hs (Quotient.mk _ b) = embed s := by
  apply Quotient.sound
  intro eps heps
  refine ⟨0, ?_⟩
  intro j _
  have he := (distance_zero_iff_stateEquiv
    (prefixState b w T s j) s).mpr
      (zero_time_prefix b w T s j hzero)
  have hself := stateSub_self_norm_zero s
  have hle : Fraction.le (distance (prefixState b w T s j) s)
      (distance s s) := Fraction.le_of_equiv
    (Fraction.equiv_trans he (Fraction.equiv_symm hself))
  exact Fraction.magnitudes.lt_of_le_lt hle
    (distance_self_lt s eps heps)

theorem zero_state_norm_value (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (hzero : (stateNorm s).num = 0) :
    gammaValue w T s hT hs (Quotient.mk _ b) = embed s := by
  have hC : (stateTimeFactor w s).num = 0 := by
    unfold stateTimeFactor Fraction.mul
    dsimp
    simp only [hzero, Int.mul_zero, Int.zero_mul]
  calc
    gammaValue w T s hT hs (Quotient.mk _ b) =
        gammaValue w T s hT hs (leftTime T hT) := by
      apply Quotient.sound
      intro eps heps
      refine ⟨0, ?_⟩
      intro j _
      have hb := prefix_time_bound b leftAddress w T s j hT hs
      have hz : (Fraction.mul
          (distance (timeState b T j) (timeState leftAddress T j))
          (stateTimeFactor w s)).num = 0 := by
        unfold Fraction.mul
        dsimp
        simp [hC]
      have hstrict : Fraction.lt
          (Fraction.mul
            (distance (timeState b T j) (timeState leftAddress T j))
            (stateTimeFactor w s)) eps := by
        unfold Fraction.lt
        simp only [hz, Int.zero_mul]
        exact Int.mul_pos heps
          (Fraction.mul
            (distance (timeState b T j) (timeState leftAddress T j))
            (stateTimeFactor w s)).den_pos
      exact Fraction.magnitudes.lt_of_le_lt hb hstrict
    _ = embed s := left_endpoint_value w T s hT hs

private def sampleOne : Fraction := ⟨1, 1, by decide⟩
private def sampleZero : Fraction := ⟨0, 1, by decide⟩
private def sampleQuarter : Fraction := ⟨1, 4, by decide⟩
private def sampleState : Point × Point :=
  ((sampleOne, sampleZero), (sampleZero, sampleOne))

theorem sample_alias_counts :
    ticks firstAlias 2 = 2 ∧ ticks secondAlias 2 = 1 := by decide

theorem sample_alias_time_gap :
    Fraction.equiv
      (distance (timeState firstAlias sampleQuarter 2)
        (timeState secondAlias sampleQuarter 2))
      ⟨1, 16, by decide⟩ := by decide

theorem sample_state_time_factor :
    Fraction.equiv (stateTimeFactor sampleOne sampleState)
      (Fraction.ofInt 8) := by decide

theorem sample_alias_bound :
    Fraction.equiv
      (Fraction.mul (distance
        (timeState firstAlias sampleQuarter 2)
        (timeState secondAlias sampleQuarter 2))
        (stateTimeFactor sampleOne sampleState))
      ⟨1, 2, by decide⟩ := by decide

theorem sample_alias_actual_error :
    Fraction.equiv
      (distance
        (prefixState firstAlias sampleOne sampleQuarter sampleState 2)
        (prefixState secondAlias sampleOne sampleQuarter sampleState 2))
      ⟨8927, 65536, by decide⟩ := by decide

theorem sample_right_ne_left :
    gammaValue sampleOne sampleQuarter sampleState
      (by decide) (by unfold DyadicSmallTime Fraction.le; decide)
      (rightTime sampleQuarter (by decide)) ≠
    gammaValue sampleOne sampleQuarter sampleState
      (by decide) (by unfold DyadicSmallTime Fraction.le; decide)
      (leftTime sampleQuarter (by decide)) := by
  have hneq := CauchyValues.sample_endpoint_value_ne_initial
  change endpointValue sampleOne sampleQuarter sampleState
    (by decide) (by unfold DyadicSmallTime Fraction.le; decide) ≠
    embed sampleState at hneq
  intro h
  apply hneq
  calc
    endpointValue sampleOne sampleQuarter sampleState
        (by decide) (by unfold DyadicSmallTime Fraction.le; decide) =
        gammaValue sampleOne sampleQuarter sampleState
          (by decide) (by unfold DyadicSmallTime Fraction.le; decide)
          (rightTime sampleQuarter (by decide)) :=
      (right_endpoint_value _ _ _ _ _).symm
    _ = gammaValue sampleOne sampleQuarter sampleState
          (by decide) (by unfold DyadicSmallTime Fraction.le; decide)
          (leftTime sampleQuarter (by decide)) := h
    _ = embed sampleState := left_endpoint_value _ _ _ _ _

end NewtonLimitDynamics.Polygon.HarmonicTimeRealization
