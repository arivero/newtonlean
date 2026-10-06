import BarrowLib.Polygon.LatticeGeometry

/-! Euclid, Elements, Book I.
Source: https://mathcs.clarku.edu/~djoyce/elements/bookI/propI37.html
Triangles on the same base between the same parallels. The retained parallel_identity is the integer-coordinate special case with base from the origin to q and third vertex translated parallel to q. It proves determinant preservation, not the full synthetic Euclidean area semantics.
Status: modern_reconstruction of this classical coordinate special case;
not an assertion that Newton explicitly cites the proposition by number.
The existing proof and qualified name are preserved. -/

namespace NewtonLimitDynamics.Polygon

theorem parallel_identity (q x : LatticePoint) (j : Int) : det q (kick q x j) = det q x := by
  simp only [det, kick, Int.mul_add]
  have h : q.1 * (j * q.2) = q.2 * (j * q.1) := by ac_rfl
  omega


end NewtonLimitDynamics.Polygon
