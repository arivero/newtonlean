import BarrowLib.Polygon.ConvexCover

/-! Rational affine lines and parallelogram intersection. Determinants express
transverse coordinates; they do not express distances or time derivatives.
No force or limiting premise is part of this elementary geometry. -/

namespace NewtonLimitDynamics.Polygon.Parallelogram
open NewtonLimitDynamics TimeSubdivision

/-- The line through `base` parallel to a nonzero `direction`. A zero
direction makes this predicate the entire plane, so uniqueness below requires
independent directions. -/
def ParallelThrough (p base direction : Point) : Prop :=
  Fraction.equiv (det p direction) (det base direction)

def diagonal (p u v : Point) : Point := pointAdd (pointAdd p u) v

/-- Adding a displacement parallel to a line leaves its transverse coordinate
unchanged. Valid also for a zero displacement or direction. -/
theorem parallel_translation (p direction : Point) (k : Fraction) :
    ParallelThrough (pointAdd p (pointScale k direction)) p direction :=
  Fraction.equiv_trans (det_add_left direction p (pointScale k direction))
    (Fraction.equiv_trans
      (Fraction.add_equiv (Fraction.equiv_refl _)
        (Fraction.equiv_trans (det_scale_left k direction direction)
          (Fraction.equiv_trans (Fraction.mul_equiv_left k (det_self direction))
            (Fraction.mul_zero k))))
      (Fraction.add_zero _))

/-- Every affine chord point lies on its endpoint line. The parameter need
not lie in the unit interval for this line-incidence statement. -/
theorem segment_on_line (a : Fraction) (p q : Point) :
    ParallelThrough (ConvexCover.lerp a p q) p (pointSub q p) := by
  have he : pointEquiv (ConvexCover.lerp a p q)
      (pointAdd p (pointScale a (pointSub q p))) := by
    constructor <;>
      simp only [ConvexCover.lerp,ConvexCover.complement,pointEquiv,pointSub,
        pointNeg,pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
        Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub,Int.neg_mul,Int.mul_neg] <;>
      ac_nf <;> omega
  exact Fraction.equiv_trans
    (det_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
    (parallel_translation p (pointSub q p) a)

/-- The opposite corner lies on both endpoint lines. -/
theorem diagonal_on_lines (p u v : Point) :
    ParallelThrough (diagonal p u v) (pointAdd p u) v ∧
    ParallelThrough (diagonal p u v) (pointAdd p v) u := by
  constructor
  · exact Fraction.equiv_trans (det_add_left v (pointAdd p u) v)
      (Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _) (det_self v))
        (Fraction.add_zero _))
  · have he : pointEquiv (diagonal p u v) (pointAdd (pointAdd p v) u) := by
      constructor <;>
        simp only [diagonal,pointAdd,Fraction.equiv,Fraction.add,
          Int.add_mul,Int.mul_add] <;> ac_nf
    exact Fraction.equiv_trans (det_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (Fraction.equiv_trans (det_add_left u (pointAdd p v) u)
        (Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _) (det_self u))
          (Fraction.add_zero _)))

/-- Two independent parallel endpoint lines meet only at the opposite corner.
The endpoint is derived from the two line constraints, not assumed. -/
theorem intersection_unique (p u v x : Point) (h : (det u v).num ≠ 0)
    (hx : ParallelThrough x (pointAdd p u) v)
    (hy : ParallelThrough x (pointAdd p v) u) :
    pointEquiv x (diagonal p u v) :=
  det_coordinates_injective u v h
    (Fraction.equiv_trans hx (Fraction.equiv_symm (diagonal_on_lines p u v).1))
    (Fraction.equiv_trans hy (Fraction.equiv_symm (diagonal_on_lines p u v).2))

end NewtonLimitDynamics.Polygon.Parallelogram
