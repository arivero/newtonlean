import BarrowLib.Polygon.LatticeGeometry

/-! Euclid, Elements, Book I.
Source: https://mathcs.clarku.edu/~djoyce/elements/bookI/propI38.html
Triangles on equal bases between the same parallels. The retained extension_identity is the integer-coordinate special case of consecutive equal collinear bases and the fixed opposite vertex at the origin. It proves determinant preservation, not the full synthetic Euclidean theorem.
Status: modern_reconstruction of this classical coordinate special case;
not an assertion that Newton explicitly cites the proposition by number.
The existing proof and qualified name are preserved. -/

namespace NewtonLimitDynamics.Polygon

theorem extension_identity (p q : LatticePoint) : det q (extend p q) = det p q := by
  simp only [det, extend, Int.mul_sub, Int.mul_assoc]
  have h : q.1 * (2 * q.2) = q.2 * (2 * q.1) := by ac_rfl
  have h1 : q.1 * p.2 = p.2 * q.1 := Int.mul_comm _ _
  have h2 : q.2 * p.1 = p.1 * q.2 := Int.mul_comm _ _
  omega


end NewtonLimitDynamics.Polygon
