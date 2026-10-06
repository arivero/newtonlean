import BarrowLib.Common.RationalMagnitudes

namespace NewtonLimitDynamics.Polygon.HarmonicTimeRealization
open NewtonLimitDynamics

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


end NewtonLimitDynamics.Polygon.HarmonicTimeRealization
