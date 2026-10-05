import BarrowLib.Polygon.FiniteEstimates

/-! A finite telescoping estimate for any rational-valued distance with a
zero diagonal and triangle inequality. No map or limiting premise is used. -/

namespace NewtonLimitDynamics.Polygon.FiniteSequenceGap
open NewtonLimitDynamics
open TimeSubdivision

theorem finite_gap (D : (Point × Point) → (Point × Point) → Fraction)
    (hz : ∀ s, Fraction.equiv (D s s) (Fraction.ofInt 0))
    (htri : ∀ s t u, Fraction.le (D s u) (Fraction.add (D s t) (D t u)))
    (f : Nat → Point × Point) (N : Nat) (C : Fraction)
    (hstep : ∀ i, i < N → Fraction.le (D (f (i+1)) (f i)) C) :
    (n k : Nat) → n+k ≤ N →
      Fraction.le (D (f (n+k)) (f n)) (Fraction.mul (Fraction.ofInt (k : Int)) C)
  | n, 0, _ => Fraction.le_of_equiv (Fraction.equiv_trans (hz (f n)) (by
      simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_zero]
      simp))
  | n, k+1, hnk => by
      have hp := finite_gap D hz htri f N C hstep n k (by omega)
      have hs := hstep (n+k) (by omega)
      have hb := Fraction.magnitudes.le_trans (htri (f (n+(k+1))) (f (n+k)) (f n))
        (Fraction.add_le_add hs hp)
      apply Fraction.le_equiv_right hb
      simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
      ac_nf

end NewtonLimitDynamics.Polygon.FiniteSequenceGap
