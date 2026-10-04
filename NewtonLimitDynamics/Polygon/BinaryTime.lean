import NewtonLimitDynamics.Polygon.CauchyValues

/-!
Binary-address time names built from the same dyadic tick counts as the actual
harmonic prefixes. The quotient below is a constructed binary-time domain;
no identification with an external real interval is asserted.
-/

namespace NewtonLimitDynamics.Polygon.BinaryTime

open NewtonLimitDynamics
open TimeSubdivision
open HarmonicStability
open HarmonicDyadic
open HarmonicBinaryPrefix
open HarmonicTimeComparison
open PointBounds
open HarmonicComparison
open HarmonicAccumulation
open CauchyValues

private def zero : Fraction := ⟨0, 1, by decide⟩

def timeApprox (b : Nat → Bool) (T : Fraction) (j : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt (ticks b j : Int)) (duration T j)

def scalarState (t : Fraction) : Point × Point :=
  ((t, zero), (zero, zero))

def timeState (b : Nat → Bool) (T : Fraction) (j : Nat) : Point × Point :=
  scalarState (timeApprox b T j)

theorem scalarState_distance (t u : Fraction) :
    Fraction.equiv (distance (scalarState t) (scalarState u))
      (durationDifference u t).abs := by
  simp only [distance, scalarState, stateNorm, stateSub, pointNorm,
    pointSub, pointAdd, pointNeg, durationDifference, negF,
    Fraction.equiv, Fraction.abs, Fraction.add, Fraction.mul, zero]
  simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
    Int.natAbs_zero, Int.ofNat_zero, Int.neg_zero,
    Int.mul_one, Int.one_mul]

theorem timeState_distance (b c : Nat → Bool) (T : Fraction) (j : Nat) :
    Fraction.equiv (distance (timeState b T j) (timeState c T j))
      (durationDifference (timeApprox c T j) (timeApprox b T j)).abs :=
  scalarState_distance _ _

theorem time_step_difference (b : Nat → Bool) (T : Fraction) (j : Nat) :
    Fraction.equiv
      (durationDifference (timeApprox b T j) (timeApprox b T (j + 1)))
      (Fraction.mul (Fraction.ofInt (bit b j : Int)) (duration T (j + 1))) := by
  simp only [timeApprox, durationDifference, negF, Fraction.equiv,
    Fraction.add, Fraction.mul, Fraction.ofInt, duration,
    ticks_next, Int.natCast_add, Int.pow_succ]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.one_mul, Int.mul_one]
  simp only [show (2 : Int) = 1 + 1 by rfl,
    Int.add_mul, Int.mul_add]
  ac_nf <;> omega

theorem adjacent_time_bound (b : Nat → Bool) (T : Fraction) (j : Nat)
    (hT : 0 ≤ T.num) :
    Fraction.le (distance (timeState b T (j + 1)) (timeState b T j))
      (duration T (j + 1)) := by
  let h := duration T (j + 1)
  let k := Fraction.ofInt (bit b j : Int)
  have h₁ := scalarState_distance (timeApprox b T (j + 1))
    (timeApprox b T j)
  have h₂ := Fraction.abs_equiv (time_step_difference b T j)
  have h₃ := Fraction.abs_mul k h
  have hk : 0 ≤ k.num := Int.ofNat_nonneg _
  have hkab := Fraction.abs_of_nonnegative k hk
  have hhab := Fraction.abs_of_nonnegative h hT
  have h₄ := HarmonicDyadic.mul_equiv hkab hhab
  have he := Fraction.equiv_trans h₁
    (Fraction.equiv_trans h₂ (Fraction.equiv_trans h₃ h₄))
  have hkone : Fraction.le k (Fraction.ofInt 1) := by
    unfold Fraction.le Fraction.ofInt
    dsimp
    simp only [Int.mul_one, Int.one_mul]
    exact Int.ofNat_le.mpr (bit_le_one b j)
  have hm := Fraction.mul_le_mul_nonnegative hkone h hT
  have hone : Fraction.equiv (Fraction.mul (Fraction.ofInt 1) h) h := by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    simp
  have hbound := Fraction.le_equiv_right hm hone
  exact Fraction.le_equiv_left he hbound

def doubleTail (T : Fraction) (j : Nat) : Fraction :=
  ⟨2 * T.num, T.den * (2 : Int) ^ j,
    Int.mul_pos T.den_pos (Int.pow_pos (by decide))⟩

theorem tail_double (T : Fraction) (j : Nat) :
    Fraction.equiv (Fraction.add (duration T j) (duration T j))
      (doubleTail T j) := by
  simp only [duration, doubleTail, Fraction.equiv, Fraction.add]
  simp only [show (2 : Int) = 1 + 1 by rfl, Int.add_mul, Int.mul_add]
  ac_nf

theorem finite_gap_time (b : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) :
    (k j : Nat) → Fraction.le
      (distance (timeState b T (j + k)) (timeState b T j))
      (duration T j)
  | 0, j => by
      have hz : Fraction.le (Fraction.ofInt 0) (duration T j) := by
        simp only [Fraction.le, Fraction.ofInt, duration]
        simp only [Int.zero_mul, Int.mul_one]
        exact hT
      simpa only [Nat.add_zero] using
        Fraction.le_equiv_left
          (stateSub_self_norm_zero (timeState b T j)) hz
  | k + 1, j => by
      have htri := stateSub_triangle
        (timeState b T (j + (k + 1)))
        (timeState b T (j + 1)) (timeState b T j)
      have hk : Fraction.le
          (distance (timeState b T (j + (k + 1)))
            (timeState b T (j + 1))) (duration T (j + 1)) := by
        simpa only [Nat.add_succ, Nat.succ_add, Nat.add_assoc] using
          finite_gap_time b T hT k (j + 1)
      have ha := adjacent_time_bound b T j hT
      have hsum := Fraction.add_le_add hk ha
      exact Fraction.le_equiv_right
        (Fraction.magnitudes.le_trans htri hsum)
        (Fraction.equiv_symm (duration_halving T j))

theorem two_sided_time (b : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) (N m n : Nat) (hm : N ≤ m) (hn : N ≤ n) :
    Fraction.le (distance (timeState b T m) (timeState b T n))
      (doubleTail T N) := by
  have hm' : N + (m - N) = m := by omega
  have hn' : N + (n - N) = n := by omega
  have hfirst := finite_gap_time b T hT (m - N) N
  have hsecond := finite_gap_time b T hT (n - N) N
  rw [hm'] at hfirst
  rw [hn'] at hsecond
  have hsecond' := Fraction.le_equiv_left
    (stateSub_norm_symm (timeState b T N) (timeState b T n)) hsecond
  have htri := stateSub_triangle
    (timeState b T m) (timeState b T N) (timeState b T n)
  exact Fraction.le_equiv_right
    (Fraction.magnitudes.le_trans htri (Fraction.add_le_add hfirst hsecond'))
    (tail_double T N)

def modulus (T eps : Fraction) : Nat := (2 * T.num * eps.den).toNat

theorem doubleTail_lt_tolerance (T eps : Fraction)
    (hT : 0 ≤ T.num) (heps : 0 < eps.num) :
    Fraction.lt (doubleTail T (modulus T eps)) eps := by
  let N := modulus T eps
  have hL : 0 ≤ 2 * T.num * eps.den :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) hT)
      (Int.le_of_lt eps.den_pos)
  have hN : (N : Int) = 2 * T.num * eps.den := Int.toNat_of_nonneg hL
  have hpow := two_pow_ge_succ N
  have hp : 0 ≤ (2 : Int) ^ N := Int.le_of_lt (Int.pow_pos (by decide))
  have hfactor : 1 ≤ eps.num * T.den := by
    have hmul := Int.mul_pos heps T.den_pos
    omega
  have hmult := Int.mul_le_mul_of_nonneg_right hfactor hp
  simp only [Int.one_mul] at hmult
  unfold Fraction.lt doubleTail
  dsimp
  change 2 * T.num * eps.den < eps.num * (T.den * (2 : Int) ^ N)
  rw [← Int.mul_assoc]
  omega

theorem time_cauchy (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num) :
    ∀ eps : Fraction, 0 < eps.num →
      ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
        Fraction.lt (distance (timeState b T m) (timeState b T n)) eps := by
  intro eps heps
  refine ⟨modulus T eps, ?_⟩
  intro m n hm hn
  exact Fraction.magnitudes.lt_of_le_lt
    (two_sided_time b T hT _ m n hm hn)
    (doubleTail_lt_tolerance T eps hT heps)

def timeName (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num) :
    EndpointCauchyName where
  approx := timeState b T
  cauchy := time_cauchy b T hT

def timeValue (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num) : Value :=
  realize (timeName b T hT)

def AddressEquiv (T : Fraction) (hT : 0 ≤ T.num)
    (b c : Nat → Bool) : Prop :=
  NameEquiv (timeName b T hT) (timeName c T hT)

theorem addressEquiv_refl (T : Fraction) (hT : 0 ≤ T.num)
    (b : Nat → Bool) : AddressEquiv T hT b b := nameEquiv_refl _

theorem addressEquiv_symm (T : Fraction) (hT : 0 ≤ T.num)
    {b c : Nat → Bool} (h : AddressEquiv T hT b c) :
    AddressEquiv T hT c b := nameEquiv_symm h

theorem addressEquiv_trans (T : Fraction) (hT : 0 ≤ T.num)
    {a b c : Nat → Bool} (hab : AddressEquiv T hT a b)
    (hbc : AddressEquiv T hT b c) : AddressEquiv T hT a c :=
  nameEquiv_trans hab hbc

def addressSetoid (T : Fraction) (hT : 0 ≤ T.num) : Setoid (Nat → Bool) where
  r := AddressEquiv T hT
  iseqv := ⟨addressEquiv_refl T hT,
    @addressEquiv_symm T hT, @addressEquiv_trans T hT⟩

def BinaryTime (T : Fraction) (hT : 0 ≤ T.num) :=
  Quotient (addressSetoid T hT)

end NewtonLimitDynamics.Polygon.BinaryTime
