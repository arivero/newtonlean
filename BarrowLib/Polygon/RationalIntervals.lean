import BarrowLib.Polygon.DyadicArithmetic

/-! Elementary rational interval bisection and gap identities. -/
namespace NewtonLimitDynamics.Polygon.RationalIntervals
open NewtonLimitDynamics
open HarmonicTimeComparison

theorem half_equiv {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv a.half b.half := by
  change a.num*(2*b.den) = b.num*(2*a.den)
  calc
    _ = 2*(a.num*b.den) := by ac_rfl
    _ = 2*(b.num*a.den) := congrArg (fun n : Int => 2*n) h
    _ = _ := by ac_rfl

theorem half_le {a b : Fraction} (h : Fraction.le a b) :
    Fraction.le a.half b.half := by
  change a.num*(2*b.den) ≤ b.num*(2*a.den)
  calc
    _ = 2*(a.num*b.den) := by ac_rfl
    _ ≤ 2*(b.num*a.den) := Int.mul_le_mul_of_nonneg_left h (by decide)
    _ = _ := by ac_rfl

theorem half_double (a : Fraction) :
    Fraction.equiv (Fraction.add a a).half a := by
  simp only [Fraction.equiv,Fraction.half,Fraction.add]
  simp only [show (2 : Int) = 1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

def midpoint (a b : Fraction) : Fraction := (Fraction.add a b).half

theorem midpoint_between (a b : Fraction) (h : Fraction.le a b) :
    Fraction.le a (midpoint a b) ∧ Fraction.le (midpoint a b) b := by
  constructor
  · exact Fraction.le_equiv_left (Fraction.equiv_symm (half_double a))
      (half_le (Fraction.add_le_add_left h a))
  · exact Fraction.le_equiv_right (half_le (Fraction.add_le_add_right h b))
      (half_double b)

theorem midpoint_lower_gap (a b : Fraction) :
    Fraction.equiv (durationDifference a (midpoint a b))
      (durationDifference a b).half := by
  simp only [midpoint,durationDifference,HarmonicStability.negF,Fraction.equiv,
    Fraction.half,Fraction.add,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
  simp only [show (2 : Int) = 1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf
  omega

theorem midpoint_upper_gap (a b : Fraction) :
    Fraction.equiv (durationDifference (midpoint a b) b)
      (durationDifference a b).half := by
  simp only [midpoint,durationDifference,HarmonicStability.negF,Fraction.equiv,
    Fraction.half,Fraction.add,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
  simp only [show (2 : Int) = 1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf
  omega

end NewtonLimitDynamics.Polygon.RationalIntervals
