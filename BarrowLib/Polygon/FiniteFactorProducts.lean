import BarrowLib.Common.FiniteGrowth
import BarrowLib.Polygon.FinitePower

/-! Elementary repeated two-factor growth, with arbitrary rational increments.
The common-denominator proof is shared by calibrated and unit-gauge estimates.
No motion, limit or differential equation is a premise. -/

namespace NewtonLimitDynamics.Polygon.FiniteFactorProducts
open NewtonLimitDynamics
open HarmonicAccumulation

def pairWeights (P Q : Fraction) : Nat → List Int
  | 0 => []
  | n+1 => [P.num * Q.den, Q.num * P.den] ++ pairWeights P Q n

theorem pairWeights_nonnegative (P Q : Fraction)
    (hP : 0 ≤ P.num) (hQ : 0 ≤ Q.num) :
    (n : Nat) → FiniteGrowth.Nonnegative (pairWeights P Q n)
  | 0 => by simp [pairWeights, FiniteGrowth.Nonnegative]
  | n+1 => by
      intro a ha
      simp only [pairWeights,List.mem_append,List.mem_cons,List.mem_nil_iff,
        or_false] at ha
      rcases ha with (rfl | rfl) | ha
      · exact Int.mul_nonneg hP (Int.le_of_lt Q.den_pos)
      · exact Int.mul_nonneg hQ (Int.le_of_lt P.den_pos)
      · exact pairWeights_nonnegative P Q hP hQ n a ha

theorem pairWeights_sum (P Q : Fraction) :
    (n : Nat) → FiniteGrowth.weightSum (pairWeights P Q n) =
      (n : Int) * (P.num * Q.den + Q.num * P.den)
  | 0 => by simp [pairWeights,FiniteGrowth.weightSum]
  | n+1 => by
      simp only [pairWeights,FiniteGrowth.weightSum_append,FiniteGrowth.weightSum,
        pairWeights_sum P Q n,Int.natCast_add,Int.natCast_one,
        Int.add_mul,Int.one_mul]
      omega

theorem pair_product (P Q : Fraction) :
    FiniteGrowth.amplification (P.den * Q.den)
      (Int.mul_pos P.den_pos Q.den_pos) [P.num * Q.den,Q.num * P.den] =
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) P)
        (Fraction.add (Fraction.ofInt 1) Q)).toRat := by
  have hp : (P.den : Rat) ≠ 0 := by simp [Int.ne_of_gt P.den_pos]
  have hq : (Q.den : Rat) ≠ 0 := by simp [Int.ne_of_gt Q.den_pos]
  simp only [FiniteGrowth.amplification,FiniteGrowth.factorProduct,
    List.length_cons,List.length_nil,Fraction.toRat,Fraction.mul,Fraction.add,
    Fraction.ofInt,Int.pow_succ,Int.pow_zero,Int.one_mul,Int.mul_one,
    Rat.intCast_mul,Rat.intCast_add]
  grind

theorem repeated_pair_product (P Q : Fraction) :
    (n : Nat) → FiniteGrowth.amplification (P.den * Q.den)
        (Int.mul_pos P.den_pos Q.den_pos) (pairWeights P Q n) =
      (fpower (Fraction.mul (Fraction.add (Fraction.ofInt 1) P)
        (Fraction.add (Fraction.ofInt 1) Q)) n).toRat
  | 0 => by
      simp only [pairWeights,FiniteGrowth.amplification,FiniteGrowth.factorProduct,
        List.length_nil,Int.pow_zero,fpower,Fraction.toRat_ofInt,Rat.intCast_one]
      grind
  | n+1 => by
      change FiniteGrowth.amplification _ _
        ([P.num * Q.den,Q.num * P.den] ++ pairWeights P Q n) =
        (Fraction.mul _ (fpower _ n)).toRat
      rw [FiniteGrowth.amplification_append,Fraction.toRat_mul,pair_product,
        repeated_pair_product]

/-- The sum of increments, rather than a dimensioned expression `1+L`,
controls the shared finite product. -/
theorem repeated_pair_le_two (P Q : Fraction) (n : Nat)
    (hP : 0 ≤ P.num) (hQ : 0 ≤ Q.num)
    (hs : Fraction.le
      (Fraction.mul (Fraction.ofInt (n : Int)) (Fraction.add P Q))
      ⟨1,2,by decide⟩) :
    Fraction.le (fpower (Fraction.mul (Fraction.add (Fraction.ofInt 1) P)
      (Fraction.add (Fraction.ofInt 1) Q)) n) (Fraction.ofInt 2) := by
  have hsmall : 2 * FiniteGrowth.weightSum (pairWeights P Q n) ≤ P.den * Q.den := by
    rw [pairWeights_sum]
    unfold Fraction.le Fraction.mul Fraction.add Fraction.ofInt at hs
    dsimp at hs
    simp only [Int.one_mul,Int.mul_one] at hs
    simpa only [Int.mul_comm,Int.mul_left_comm,Int.mul_assoc] using hs
  apply (Fraction.le_iff_toRat _ _).mpr
  rw [Fraction.toRat_ofInt,Rat.intCast_ofNat,← repeated_pair_product P Q n]
  exact FiniteGrowth.uniform_amplification _ _ (pairWeights P Q n)
    (pairWeights_nonnegative P Q hP hQ n) hsmall

theorem fpower_congr {r q : Fraction} (hrq : Fraction.equiv r q) :
    (n : Nat) → Fraction.equiv (fpower r n) (fpower q n)
  | 0 => Fraction.equiv_refl _
  | n+1 => Fraction.mul_equiv hrq (fpower_congr hrq n)

theorem fpower_square (r : Fraction) :
    (n : Nat) → Fraction.equiv (fpower (Fraction.mul r r) n) (fpower r (2*n))
  | 0 => by simp [fpower,Fraction.equiv,Fraction.ofInt]
  | n+1 => by
      simp only [Nat.mul_succ,Nat.add_succ,Nat.add_zero,fpower]
      exact Fraction.equiv_trans
        (Fraction.mul_equiv (Fraction.equiv_refl _) (fpower_square r n))
        (Fraction.mul_assoc r r (fpower r (2*n)))

end NewtonLimitDynamics.Polygon.FiniteFactorProducts
