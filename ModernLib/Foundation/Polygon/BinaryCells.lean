import ModernLib.Foundation.Polygon.AffineValues

/-! Rational coarse-cell intervals and the adjacent-cell alternatives for
equivalent binary addresses. These facts contain no mechanical premises. -/

namespace NewtonLimitDynamics.Polygon.BinaryTime
open NewtonLimitDynamics
open HarmonicBinaryPrefix HarmonicDyadic HarmonicTimeComparison

-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
theorem count_duration_monotone (T : Fraction) (m : Nat)
    (hT : 0 ≤ T.num) (i k : Nat) (hik : i ≤ k) :
    Fraction.le (Fraction.mul (Fraction.ofInt (i:Int)) (duration T m))
      (Fraction.mul (Fraction.ofInt (k:Int)) (duration T m)) := by
  apply Fraction.mul_le_mul_nonnegative (c:=duration T m) (hc:=hT)
  simp only [Fraction.le, Fraction.ofInt, Int.mul_one]
  exact Int.ofNat_le.mpr hik

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem coarse_upper (b : Nat → Bool) (T : Fraction) (m : Nat) :
    Fraction.equiv (Fraction.add (timeApprox b T m) (duration T m))
      (Fraction.mul (Fraction.ofInt ((ticks b m+1:Int))) (duration T m)) := by
  simp only [timeApprox, Fraction.equiv, Fraction.add, Fraction.mul,
    Fraction.ofInt, Int.add_mul, Int.mul_add]
  ac_nf

-- Modern dependency score: 7/51 (M=7, H=44; transitive project theorems/axioms).
theorem time_interval (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m j : Nat) :
    Fraction.le (timeApprox b T m) (timeApprox b T (m+j)) ∧
    Fraction.le (timeApprox b T (m+j))
      (Fraction.add (timeApprox b T m) (duration T m)) := by
  have hs := AffineValues.phase_interval b T hT m j
  exact ⟨(difference_nonnegative_iff _ _).mp hs.1,
    difference_add_bound _ _ _ hs.2⟩

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem coarse_two_step (b : Nat → Bool) (T : Fraction) (m : Nat) :
    Fraction.equiv
      (Fraction.add (Fraction.add (timeApprox b T m) (duration T m)) (duration T m))
      (Fraction.mul (Fraction.ofInt ((ticks b m+2:Int))) (duration T m)) := by
  simp only [timeApprox, Fraction.equiv, Fraction.add, Fraction.mul,
    Fraction.ofInt, Int.add_mul, Int.mul_add]
  simp only [show (2:Int)=1+1 by rfl, Int.mul_add, Int.mul_one]
  ac_nf
  simp only [Int.mul_add, Int.mul_one, Int.add_mul]
  ac_nf

-- Modern dependency score: 10/56 (M=10, H=46; transitive project theorems/axioms).
theorem separated_cell_time_gap (b c : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) (m j : Nat) (hgap : ticks b m + 2 ≤ ticks c m) :
    Fraction.le (duration T m)
      (durationDifference (timeApprox b T (m+j)) (timeApprox c T (m+j))).abs := by
  obtain ⟨_,hb⟩ := time_interval b T hT m j
  obtain ⟨hc,_⟩ := time_interval c T hT m j
  have hbc := count_duration_monotone T m hT (ticks b m+2) (ticks c m) hgap
  have hbig := Fraction.magnitudes.le_trans
    (Fraction.add_le_add_right hb (duration T m))
    (Fraction.magnitudes.le_trans
      (Fraction.le_equiv_left (coarse_two_step b T m) hbc) hc)
  have hd := Fraction.le_add_cancel_left (timeApprox b T (m+j)) (duration T m)
    (durationDifference (timeApprox b T (m+j)) (timeApprox c T (m+j)))
    (Fraction.le_equiv_right hbig
      (Fraction.equiv_symm (add_difference_cancel _ _)))
  exact Fraction.magnitudes.le_trans hd (Fraction.le_abs _)

-- Modern dependency score: 17/72 (M=17, H=55; transitive project theorems/axioms).
theorem address_equiv_no_separated_cells (b c : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) (hpos : 0 < T.num) (m : Nat)
    (ht : AddressEquiv T hT b c) : ¬ ticks b m + 2 ≤ ticks c m := by
  intro hc
  obtain ⟨N,hN⟩ := addressEquiv_symm T hT ht (duration T m) hpos
  have hsmall := hN (m+N) (by omega)
  have hbound := separated_cell_time_gap b c T hT m N hc
  have hd := timeState_distance c b T (m+N)
  have hlow := Fraction.le_equiv_right hbound (Fraction.equiv_symm hd)
  exact Fraction.magnitudes.lt_irrefl _
    (Fraction.magnitudes.lt_of_le_lt hlow hsmall)

-- Modern dependency score: 18/73 (M=18, H=55; transitive project theorems/axioms).
theorem address_equiv_cell_cases (b c : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) (hpos : 0 < T.num) (m : Nat)
    (ht : AddressEquiv T hT b c) :
    ticks b m = ticks c m ∨ ticks b m + 1 = ticks c m ∨
      ticks c m + 1 = ticks b m := by
  have hnot := address_equiv_no_separated_cells b c T hT hpos m ht
  have hnotrev := address_equiv_no_separated_cells c b T hT hpos m
    (addressEquiv_symm T hT ht)
  omega

end NewtonLimitDynamics.Polygon.BinaryTime
