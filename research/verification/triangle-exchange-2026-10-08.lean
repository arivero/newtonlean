import BarrowLib

/-! Target pin and exact controls for finite triangle exchange.
For positive horizontal original vertices A,Q with nonnegative determinant,
every point of O,A,Q lies in O,A,P or A,P,Q or O,P,Q, with arbitrary rational
P. The nonzero-determinant version does not need a horizontal chart.
May assume core rational arithmetic and explicit barycentric membership only;
must derive the inserted coordinates, simplex exit and actual set inclusion.
No area rules, desired difference inclusion, modern topology or completion.

Controls: an interior inserted point requires the triangle away from O;
an exterior inserted point has negative barycentric coordinates; collinear,
coincident and shared-edge cases retain closed membership. The signed scalar
triple (2,-1,0) against (1/3,1/3,1/3) exits at t=1/6; t=1/5 is rejected.
For A=(1,0), P=(1,1/4), Q=(17/16,1/4), X=(33/32,1/8), X lies in the Q sector
and outside the P sector and terminal connector, so the one-cell cover must
use the actual square. Exact computations and general proofs share the
kernel and Fraction definitions; these controls are not independent of them.
This harness does not assert the many-cell sector-union collar or B. -/
namespace NewtonLimitDynamics.Polygon.TriangleExchangeControls
open NewtonLimitDynamics TimeSubdivision SectorFan ConvexCover TriangleExchange
local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))
private def z := Fraction.ofInt 0
private def o := Fraction.ofInt 1
private def f (n d : Int) (hd : 0<d) : Fraction := ⟨n,d,hd⟩
private def pt (x y : Int) : Point := (Fraction.ofInt x,Fraction.ofInt y)
private def h := f 1 2 (by decide)
private def third := f 1 3 (by decide)

example : ∃ t : Fraction, 0 ≤ t.num ∧ Fraction.le t o ∧
    Fraction.le (Fraction.mul t (Fraction.ofInt 2)) third ∧
    Fraction.le (Fraction.mul t (Fraction.ofInt (-1))) third ∧
    Fraction.le (Fraction.mul t z) third ∧
    (Fraction.equiv (Fraction.mul t (Fraction.ofInt 2)) third ∨
      Fraction.equiv (Fraction.mul t (Fraction.ofInt (-1))) third ∨
      Fraction.equiv (Fraction.mul t z) third) :=
  SimplexExit.simplex_exit third third third (Fraction.ofInt 2) (Fraction.ofInt (-1)) z
    (by decide) (by decide) (by decide) (by decide) (by decide)
example : Fraction.equiv (Fraction.mul (f 1 6 (by decide)) (Fraction.ofInt 2)) third := by decide
example : ¬ Fraction.le (Fraction.mul (f 1 5 (by decide)) (Fraction.ofInt 2)) third := by decide
example : ¬ Fraction.equiv (Fraction.add (Fraction.add z z) z) o := by decide

private theorem interior_membership : Triangle (pt 2 0) (pt 0 2) (pt 1 1) :=
  ⟨h,h,by decide,by decide,by decide,by constructor <;> decide⟩
example : Triangle (pt 2 0) (h,h) (pt 1 1) ∨
    TriangleAt (pt 2 0) (h,h) (pt 0 2) (pt 1 1) ∨ Triangle (h,h) (pt 0 2) (pt 1 1) :=
  exchange_independent _ _ _ _ (by decide) interior_membership
example : TriangleAt (pt 2 0) (h,h) (pt 0 2) (pt 1 1) := by
  exact ⟨z,h,by decide,by decide,by decide,by constructor <;> decide⟩

-- Exterior P=(-1,-1) has both coefficients -1/2 in these directions.
example : Fraction.equiv (Fraction.quotient
    (TimeSubdivision.det (pt (-1) (-1)) (pt 0 2))
    (TimeSubdivision.det (pt 2 0) (pt 0 2)) (by decide)) (f (-1) 2 (by decide)) := by decide
example : Triangle (pt 2 0) (pt (-1) (-1)) (pt 1 1) ∨
    TriangleAt (pt 2 0) (pt (-1) (-1)) (pt 0 2) (pt 1 1) ∨
    Triangle (pt (-1) (-1)) (pt 0 2) (pt 1 1) :=
  exchange_independent _ _ _ _ (by decide) interior_membership

private theorem collinear_membership : Triangle (pt 1 0) (pt 2 0) (f 3 2 (by decide),z) :=
  ⟨z,f 3 4 (by decide),by decide,by decide,by decide,by constructor <;> decide⟩
example : Triangle (pt 1 0) (pt 1 1) (f 3 2 (by decide),z) ∨
    TriangleAt (pt 1 0) (pt 1 1) (pt 2 0) (f 3 2 (by decide),z) ∨
    Triangle (pt 1 1) (pt 2 0) (f 3 2 (by decide),z) :=
  exchange_positive _ _ _ _ (by decide) (by decide) (by decide) collinear_membership
example : Triangle (pt 2 0) (pt 1 1) (f 3 2 (by decide),z) ∨
    TriangleAt (pt 2 0) (pt 1 1) (pt 1 0) (f 3 2 (by decide),z) ∨
    Triangle (pt 1 1) (pt 1 0) (f 3 2 (by decide),z) :=
  exchange_positive _ _ _ _ (by decide) (by decide) (by decide)
    ((triangle_swap _ _ _).mp collinear_membership)
example : Triangle (pt 1 0) (pt 1 1) (h,z) ∨
    TriangleAt (pt 1 0) (pt 1 1) (pt 1 0) (h,z) ∨ Triangle (pt 1 1) (pt 1 0) (h,z) :=
  exchange_positive _ _ _ _ (by decide) (by decide) (by decide)
    ⟨h,z,by decide,by decide,by decide,by constructor <;> decide⟩

private def a := pt 1 0
private def p : Point := (o,f 1 4 (by decide))
private def q : Point := (f 17 16 (by decide),f 1 4 (by decide))
private def x : Point := (f 33 32 (by decide),f 1 8 (by decide))
private def radius := f 11 16 (by decide)
private theorem sample_membership : Triangle a q x :=
  ⟨h,h,by decide,by decide,by decide,by constructor <;> decide⟩
private theorem outside_mechanical : ¬ Triangle a p x := by
  rintro ⟨u,v,_,_,hs,he⟩
  have he' : Fraction.equiv x.1 (Fraction.add u v) := Fraction.equiv_trans he.1 (by
    simp only [a,p,pt,o,pointScale,pointAdd,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one])
  have hn : ¬ Fraction.le x.1 o := by decide
  exact hn (Fraction.le_equiv_left he' hs)
private theorem outside_terminal : ¬ Triangle p q x := by
  intro hx
  have hn := triangle_right p q q x hx (by decide) (by decide)
  have hf : ¬ 0 ≤ (TimeSubdivision.det q x).num := by decide
  exact hf hn
example : SquareContains a radius x := by
  have hc := one_cell_difference_cover a p q x a radius (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) sample_membership outside_mechanical
  exact hc.resolve_right outside_terminal
example : ∃ r u, UnitInterval r ∧ UnitInterval u ∧
    pointEquiv x (matchedPatch r u a p a q) := by
  rcases exchange_positive a q p x (by decide) (by decide) (by decide) sample_membership with hp | hp | hp
  · exact False.elim (outside_mechanical hp)
  · exact triangleAt_common_start_patch a p q x hp
  · exact False.elim (outside_terminal hp)

#print axioms SimplexExit.simplex_exit
#print axioms TriangleExchange.exchange_positive
#print axioms TriangleExchange.one_cell_difference_cover
#print axioms MotionSampling.initial_cell_difference_cover
end NewtonLimitDynamics.Polygon.TriangleExchangeControls

/-! A hostile rational control for the finite exchange only. The inserted
point P is exterior, and X is in the interior of the translated triangle
A,P,Q while lying in neither origin cone. Coordinates and witnesses have
deliberately unnormalized denominators. -/
namespace NewtonLimitDynamics.Polygon.TriangleExchangeReview
open NewtonLimitDynamics TimeSubdivision SectorFan TriangleExchange

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num * b.den ≤ b.num * a.den))

private def f (n d : Int) (hd : 0 < d) : Fraction := ⟨n,d,hd⟩
private def a : Point := (f 2 2 (by decide), f 0 2 (by decide))
private def q : Point := (f 3 3 (by decide), f 2 2 (by decide))
private def p : Point := (f (-2) 2 (by decide), f 0 5 (by decide))
private def x : Point := (f 2 4 (by decide), f 1 4 (by decide))

private theorem original : Triangle a q x :=
  ⟨f 2 8 (by decide), f 3 12 (by decide), by decide, by decide,
    by decide, by constructor <;> decide⟩

private theorem outside_a_p : ¬ Triangle a p x := by
  intro hx
  have h := triangle_right a p p x hx (by decide) (by decide)
  have hn : ¬ 0 ≤ (TimeSubdivision.det p x).num := by decide
  exact hn h

private theorem outside_p_q : ¬ Triangle p q x := by
  intro hx
  have h := triangle_right p q q x hx (by decide) (by decide)
  have hn : ¬ 0 ≤ (TimeSubdivision.det q x).num := by decide
  exact hn h

-- This requires the translated A,P,Q cell, with both barycentric weights
-- strictly positive. The disjunction is obtained from the general theorem.
example : TriangleAt a p q x := by
  rcases exchange_positive a q p x (by decide) (by decide) (by decide) original
    with hp | hp | hp
  · exact False.elim (outside_a_p hp)
  · exact hp
  · exact False.elim (outside_p_q hp)

example : TriangleAt a p q x :=
  ⟨f 3 12 (by decide), f 2 8 (by decide), by decide, by decide,
    by decide, by constructor <;> decide⟩

#print axioms TriangleExchange.exchange_positive
end NewtonLimitDynamics.Polygon.TriangleExchangeReview
