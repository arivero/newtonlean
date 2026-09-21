import NewtonLimitDynamics.Common.RationalMagnitudes
import NewtonLimitDynamics.Principia1713.ForceComparison

namespace NewtonLimitDynamics.Contact
open Fraction

/-- The normal contact subtense, the tangent departure and the defect area
    are separate quantities. Identifying any two is an additional configuration
    hypothesis. For oblique contact subtenses an angle factor is required. -/
structure Quantities where
  tangentLength : Fraction
  chordLength : Fraction
  normalSubtense : Fraction
  tangentDeparture : Fraction
  defectArea : Fraction

theorem le_quotient_iff (a b c : Fraction) (hc : positive c) :
    le a (Principia1713.quotient b c hc) ↔ le (mul a c) b := by
  unfold le Principia1713.quotient mul
  dsimp
  have e1 : a.num * (b.den * c.num) = a.num * c.num * b.den := by ac_rfl
  have e2 : b.num * c.den * a.den = b.num * (a.den * c.den) := by ac_rfl
  rw [e1, e2]

/-- Circle identity AB²=AG*BD imported from Lemma XI case 1. A uniform
    positive lower bound on AG is essential; the identity alone is insufficient.
    This proves an inequality, not existence of the osculating configuration. -/
theorem normal_subtense_bound (chord subtense diameter minDiameter : Fraction)
    (hs : positive subtense) (hd : positive minDiameter)
    (hmin : le minDiameter diameter)
    (circle : equiv (mul diameter subtense) (mul chord chord)) :
    le subtense (Principia1713.quotient (mul chord chord) minDiameter hd) := by
  apply (le_quotient_iff _ _ _ hd).mpr
  have hc := (equiv_iff_mutual_le _ _).mp (mul_comm subtense minDiameter)
  have hm := mul_le_mul_positive hmin subtense hs
  have he := (equiv_iff_mutual_le _ _).mp circle
  exact magnitudes.le_trans hc.1 (magnitudes.le_trans hm he.1)

/-- Explicit finite cubic inequality from a rectangle enclosing the defect.
    K is a proved/assumed quadratic bound valid on the SAME neighbourhood.
    No assertion of contact or enclosure is hidden in power notation. -/
theorem cubic_rectangle_bound (base departure defect K : Fraction)
    (hb : positive base)
    (hquad : le departure (mul K (mul base base)))
    (henclose : le defect (mul departure base)) :
    le defect (mul K (mul base (mul base base))) := by
  have hm := mul_le_mul_positive hquad base hb
  have he : equiv (mul (mul K (mul base base)) base) (mul K (mul base (mul base base))) := by
    unfold equiv mul
    dsimp
    ac_rfl
  exact magnitudes.le_trans henclose (magnitudes.le_trans hm ((equiv_iff_mutual_le _ _).mp he).1)

/-- Coordinate construction for Lemma XI case 1: A=(0,0), B=(x,y),
    G=(0,D), with AB perpendicular to BG. The corresponding right-triangle
    relation yields AB²=AG*BD; existence of G and its limiting position is
    deliberately not inferred. This is a reconstruction of circle geometry. -/
theorem circle_identity_from_perpendicular (x y D : Int)
    (perpendicular : x*x + y*(y-D) = 0) : x*x+y*y = D*y := by
  rw [Int.mul_sub] at perpendicular
  have h : y*D = D*y := Int.mul_comm _ _
  omega

end NewtonLimitDynamics.Contact
