import ModernLib.Polygon.CauchyValues
import ModernLib.Foundation.Polygon.BinaryTime
import ModernLib.Foundation.Polygon.ScaledTolerance
import ModernLib.Foundation.Polygon.BinaryEndpoints
import BarrowLib.Polygon.FiniteSequenceGap

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

-- Modern dependency score: 5/17 (M=5, H=12; transitive project theorems/axioms).
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

-- Modern dependency score: 33/81 (M=33, H=48; transitive project theorems/axioms).
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

-- Modern dependency score: 44/98 (M=44, H=54; transitive project theorems/axioms).
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
    have hw := Int.natCast_nonneg w.num.natAbs
    have hd := w.den_pos
    omega
  have hm₁ := Fraction.mul_le_mul_nonnegative_left hq
    (Fraction.add (Fraction.ofInt 1) w.abs) hfac
  have hm₂ := Fraction.mul_le_mul_nonnegative_left hm₁ h hT
  have habs := Fraction.abs_of_nonnegative h hT
  have he := Fraction.mul_equiv habs
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

-- Modern dependency score: 45/111 (M=45, H=66; transitive project theorems/axioms).
theorem countState_gap (w T : Fraction) (s : Point × Point)
    (j : Nat) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    (n k : Nat) → n + k ≤ blocks j →
      Fraction.le (distance (countState w T s j (n + k))
        (countState w T s j n))
        (Fraction.mul (Fraction.ofInt (k : Int))
          (Fraction.mul (duration T j) (stateTimeFactor w s)))
  | n, k, hnk => by
      have hg := FiniteSequenceGap.finite_gap
        (fun x y => (distance x y).toRat)
        (fun x => by
          have hx := (Fraction.equiv_iff_toRat _ _).mp (stateSub_self_norm_zero x)
          simpa only [Fraction.toRat_ofInt, Rat.intCast_zero] using! hx)
        (fun x y z => by
          have ht := (Fraction.le_iff_toRat _ _).mp (stateSub_triangle x y z)
          simpa only [Fraction.toRat_add] using! ht)
        (countState w T s j) (blocks j)
        (Fraction.mul (duration T j) (stateTimeFactor w s)).toRat
        (fun i hi => (Fraction.le_iff_toRat _ _).mp
          (countState_step_bound w T s j i hT hs (Nat.le_of_lt hi))) n k hnk
      apply (Fraction.le_iff_toRat _ _).mpr
      simpa only [Fraction.toRat_mul, Fraction.toRat_ofInt, Rat.intCast_ofNat] using! hg

-- Modern dependency score: 0/3 (M=0, H=3; transitive project theorems/axioms).
theorem stateTimeFactor_nonnegative (w : Fraction) (s : Point × Point) :
    0 ≤ (stateTimeFactor w s).num := by
  unfold stateTimeFactor Fraction.mul Fraction.add Fraction.ofInt Fraction.abs
  dsimp
  have hw := Int.natCast_nonneg w.num.natAbs
  have hd := w.den_pos
  have hm := stateNorm_nonnegative s
  exact Int.mul_nonneg (by decide)
    (Int.mul_nonneg (by omega) hm)

-- Modern dependency score: 46/114 (M=46, H=68; transitive project theorems/axioms).
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
    (Fraction.mul_equiv he (Fraction.equiv_refl _))
  simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
  ac_nf

-- Modern dependency score: 47/121 (M=47, H=74; transitive project theorems/axioms).
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
      (Fraction.mul_equiv ht (Fraction.equiv_refl _))

-- Modern dependency score: 49/127 (M=49, H=78; transitive project theorems/axioms).
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
  exact Fraction.mul_equiv
    (Fraction.equiv_symm (scalarState_distance
      (timeApprox b T j) (timeApprox c T j)))
    (Fraction.equiv_refl _)

-- Modern dependency score: 120/224 (M=120, H=104; transitive project theorems/axioms).
theorem address_state_equiv (b c : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T)
    (hbc : AddressEquiv T hT b c) :
    NameEquiv (prefixName b w T s hT hs)
      (prefixName c w T s hT hs) := by
  intro eps heps
  let C := stateTimeFactor w s
  have hC := stateTimeFactor_nonnegative w s
  let delta := Fraction.ofRat (factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC))
  obtain ⟨N, hN⟩ := hbc delta ((by
      apply (Fraction.positive_iff_toRat _).mpr
      change 0 < (Fraction.ofRat _).toRat
      rw [Fraction.toRat_ofRat]
      have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
      have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
      (try dsimp only at hcoef hepsRat ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
  refine ⟨N, ?_⟩
  intro j hj
  have hb := prefix_time_bound b c w T s j hT hs
  have hsmall := (show Fraction.lt (Fraction.mul ((distance (timeState b T j) (timeState c T j))) (C)) (eps) from by
      apply (Fraction.lt_iff_toRat _ _).mpr
      rw [Fraction.toRat_mul]
      have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
      have hdist := ((Fraction.nonnegative_iff_toRat (distance (timeState b T j) (timeState c T j))).mp (stateNorm_nonnegative _))
      have hstrict := (Fraction.lt_iff_toRat _ _).mp (hN j hj)
      change (distance (timeState b T j) (timeState c T j)).toRat < (Fraction.ofRat _).toRat at hstrict
      rw [Fraction.toRat_ofRat] at hstrict
      (try dsimp only at hcoef hdist hstrict ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff])
  exact Fraction.magnitudes.lt_of_le_lt hb hsmall

def gammaValue (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    BinaryTime T hT → Value :=
  Quotient.lift
    (fun b => binaryValue b w T s hT hs)
    (fun b c hbc => Quotient.sound
      (address_state_equiv b c w T s hT hs hbc))

-- Modern dependency score: 131/236 (M=131, H=105; transitive project theorems/axioms).
theorem gammaValue_address (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) :
    gammaValue w T s hT hs (Quotient.mk _ b) =
      binaryValue b w T s hT hs := rfl

-- Modern dependency score: 140/249 (M=140, H=109; transitive project theorems/axioms).
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

def timeTolerance (w : Fraction) (s : Point × Point)
    (eps : Fraction) : Fraction :=
  Fraction.ofRat (factorDelta ((stateTimeFactor w s)).toRat (eps.half).toRat ((Fraction.nonnegative_iff_toRat (stateTimeFactor w s)).mp (stateTimeFactor_nonnegative w s)))

-- Modern dependency score: 1/10 (M=1, H=9; transitive project theorems/axioms).
theorem timeTolerance_positive (w : Fraction) (s : Point × Point)
    (eps : Fraction) (heps : 0 < eps.num) :
    0 < (timeTolerance w s eps).num :=
  (by
      apply (Fraction.positive_iff_toRat _).mpr
      change 0 < (Fraction.ofRat _).toRat
      rw [Fraction.toRat_ofRat]
      have hcoef := ((Fraction.nonnegative_iff_toRat (stateTimeFactor w s)).mp (stateTimeFactor_nonnegative w s))
      have hepsRat : 0 < (eps.half).toRat := (Fraction.positive_iff_toRat (eps.half)).mp heps
      (try dsimp only at hcoef hepsRat ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos])

-- Modern dependency score: 144/253 (M=144, H=109; transitive project theorems/axioms).
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
    ((by
        apply (Fraction.le_iff_toRat _ _).mpr
        change (Fraction.mul (Fraction.ofRat _) _).toRat ≤ Fraction.toRat _
        rw [Fraction.toRat_mul, Fraction.toRat_ofRat]
        exact HarmonicTimeRealization.factor_delta_weak _ _ ((Fraction.nonnegative_iff_toRat _).mp (stateTimeFactor_nonnegative w s)) ((Fraction.nonnegative_iff_toRat _).mp (by simpa only [Fraction.half] using Int.le_of_lt heps)))) hb

-- Modern dependency score: 1/13 (M=1, H=12; transitive project theorems/axioms).
theorem duration_factor_eventually_small (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j : Nat, N ≤ j →
      Fraction.lt (Fraction.mul (duration T j) (stateTimeFactor w s))
        eps := by
  let C := stateTimeFactor w s
  let delta := Fraction.ofRat (factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp (stateTimeFactor_nonnegative w s)))
  obtain ⟨N, hN⟩ := duration_eventually_small T delta hT
    ((by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp (stateTimeFactor_nonnegative w s))
        have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
  refine ⟨N, ?_⟩
  intro j hj
  exact (show Fraction.lt (Fraction.mul ((duration T j)) (C)) (eps) from by
      apply (Fraction.lt_iff_toRat _ _).mpr
      rw [Fraction.toRat_mul]
      have hcoef := ((Fraction.nonnegative_iff_toRat C).mp (stateTimeFactor_nonnegative w s))
      have hdist := ((Fraction.nonnegative_iff_toRat (duration T j)).mp hT)
      have hstrict := (Fraction.lt_iff_toRat _ _).mp (hN j hj)
      change Fraction.toRat _ < (Fraction.ofRat _).toRat at hstrict
      rw [Fraction.toRat_ofRat] at hstrict
      (try dsimp only at hcoef hdist hstrict ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff])

-- Modern dependency score: 132/238 (M=132, H=106; transitive project theorems/axioms).
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

-- Modern dependency score: 47/114 (M=47, H=67; transitive project theorems/axioms).
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

-- Modern dependency score: 142/248 (M=142, H=106; transitive project theorems/axioms).
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

-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
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

-- Modern dependency score: 2/10 (M=2, H=8; transitive project theorems/axioms).
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

-- Modern dependency score: 8/56 (M=8, H=48; transitive project theorems/axioms).
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

-- Modern dependency score: 19/71 (M=19, H=52; transitive project theorems/axioms).
theorem alias_time_eq (T : Fraction) (hT : 0 ≤ T.num) :
    (Quotient.mk (addressSetoid T hT) firstAlias : BinaryTime T hT) =
      Quotient.mk (addressSetoid T hT) secondAlias :=
  Quotient.sound (alias_address_equiv T hT)

-- Modern dependency score: 135/241 (M=135, H=106; transitive project theorems/axioms).
theorem alias_value_eq (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    binaryValue firstAlias w T s hT hs =
      binaryValue secondAlias w T s hT hs := by
  exact congrArg (gammaValue w T s hT hs) (alias_time_eq T hT)

-- Modern dependency score: 140/245 (M=140, H=105; transitive project theorems/axioms).
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

-- Modern dependency score: 133/239 (M=133, H=106; transitive project theorems/axioms).
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

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_alias_counts :
    ticks firstAlias 2 = 2 ∧ ticks secondAlias 2 = 1 := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_alias_time_gap :
    Fraction.equiv
      (distance (timeState firstAlias sampleQuarter 2)
        (timeState secondAlias sampleQuarter 2))
      ⟨1, 16, by decide⟩ := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_state_time_factor :
    Fraction.equiv (stateTimeFactor sampleOne sampleState)
      (Fraction.ofInt 8) := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_alias_bound :
    Fraction.equiv
      (Fraction.mul (distance
        (timeState firstAlias sampleQuarter 2)
        (timeState secondAlias sampleQuarter 2))
        (stateTimeFactor sampleOne sampleState))
      ⟨1, 2, by decide⟩ := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_alias_actual_error :
    Fraction.equiv
      (distance
        (prefixState firstAlias sampleOne sampleQuarter sampleState 2)
        (prefixState secondAlias sampleOne sampleQuarter sampleState 2))
      ⟨8927, 65536, by decide⟩ := by decide

-- Modern dependency score: 151/259 (M=151, H=108; transitive project theorems/axioms).
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
