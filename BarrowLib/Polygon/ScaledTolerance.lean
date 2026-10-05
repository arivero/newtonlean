import BarrowLib.Polygon.CauchyValues

/-! Elementary rational tolerances for scaling and monotonicity of generic
closed quotient bounds. The retained namespace is an import-compatible name;
no harmonic parameter or mechanical result is a premise. -/

namespace NewtonLimitDynamics.Polygon.HarmonicTimeRealization
open NewtonLimitDynamics
open HarmonicDyadic CauchyValues

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
  have hsum := Fraction.le_equiv_right hmul (Fraction.add_mul R delta C)
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

end NewtonLimitDynamics.Polygon.HarmonicTimeRealization
