import NewtonLimitDynamics.Polygon.Finite

/-!
Finite converse of the equal-area polygon construction (motivated by 1687
Proposition II, NATP00077 par48–49, and 1713 Proposition II, NATP00082
par58–59).  Modern integer-coordinate reconstruction with the centre S at the
origin.  Given three consecutive vertices `p, q, C` and the inertial
continuation `c = extend p q`, equality of the **oriented** doubled areas
`Spq` and `SqC` makes the deflection `C - c` parallel to `Sq`, and the step is
then a central kick with a rational impulse.  Orientation (Euclid's "same
side"), a vertex distinct from S, and the inward sense are separate premises;
counterexamples show each is needed.  No curve, limit or force law is produced.
-/

namespace NewtonLimitDynamics.Polygon.Converse

open NewtonLimitDynamics.Polygon

def sub (x y : LatticePoint) : LatticePoint := (x.1 - y.1, x.2 - y.2)

/-- The deflection from the inertial continuation `c` of `pq` to the actual
    next vertex `C` (Newton's segment `cC`). -/
def deflection (p q C : LatticePoint) : LatticePoint := sub C (extend p q)

theorem det_sub (q x y : LatticePoint) : det q (sub x y) = det q x - det q y := by
  simp only [det, sub, Int.mul_sub]
  omega

/-- The deflection's determinant with the radius `Sq` is the change of oriented
    area. -/
theorem det_deflection (p q C : LatticePoint) :
    det q (deflection p q C) = det q C - det p q := by
  unfold deflection
  rw [det_sub, extension_identity]

/-- Coordinate form of the Euclid I.39/I.40 step: equal oriented areas make the
    deflection `cC` parallel to `Sq`. -/
theorem equal_area_parallel (p q C : LatticePoint) (h : det q C = det p q) :
    det q (deflection p q C) = 0 := by
  rw [det_deflection, h, Int.sub_self]

/-- And conversely a deflection parallel to `Sq` preserves the oriented area. -/
theorem parallel_equal_area (p q C : LatticePoint) (h : det q (deflection p q C) = 0) :
    det q C = det p q := by
  rw [det_deflection] at h
  omega

/-- A vector parallel to a nonzero radius is a rational multiple of it:
    `b*d = a*q` with `b ≠ 0`. -/
theorem parallel_is_multiple (q d : LatticePoint) (hq : q ≠ (0, 0)) (h : det q d = 0) :
    ∃ a b : Int, b ≠ 0 ∧ b * d.1 = a * q.1 ∧ b * d.2 = a * q.2 := by
  unfold det at h
  by_cases h1 : q.1 = 0
  · have h2 : q.2 ≠ 0 := by
      intro h2
      apply hq
      exact Prod.ext h1 h2
    refine ⟨d.2, q.2, h2, ?_, ?_⟩
    · rw [h1, Int.mul_zero]
      rw [h1, Int.zero_mul] at h
      have : q.2 * d.1 = 0 := by omega
      exact this
    · exact Int.mul_comm _ _
  · refine ⟨d.1, q.1, h1, Int.mul_comm _ _, ?_⟩
    have : q.1 * d.2 = q.2 * d.1 := by omega
    rw [this, Int.mul_comm]

/-- Finite converse for one step: equal oriented areas and a vertex distinct
    from S give a rational central impulse `a/b` with `b*C = b*c + a*q`. -/
theorem equal_area_central_step (p q C : LatticePoint) (hq : q ≠ (0, 0))
    (h : det q C = det p q) :
    ∃ a b : Int, b ≠ 0 ∧
      b * C.1 = b * (extend p q).1 + a * q.1 ∧ b * C.2 = b * (extend p q).2 + a * q.2 := by
  obtain ⟨a, b, hb, h1, h2⟩ :=
    parallel_is_multiple q (deflection p q C) hq (equal_area_parallel p q C h)
  refine ⟨a, b, hb, ?_, ?_⟩
  · simp only [deflection, sub, Int.mul_sub] at h1
    omega
  · simp only [deflection, sub, Int.mul_sub] at h2
    omega

/-- A finite vertex sequence whose consecutive oriented triangles about S are
    all equal (equal areas in equal time cells) has every deflection parallel to
    its current radius. -/
theorem equal_areas_all_central (v : Nat → LatticePoint)
    (h : ∀ n, det (v (n + 1)) (v (n + 2)) = det (v n) (v (n + 1))) (n : Nat) :
    det (v (n + 1)) (deflection (v n) (v (n + 1)) (v (n + 2))) = 0 :=
  equal_area_parallel _ _ _ (h n)

/-- Orientation is needed: equal unsigned areas (`det q C = -det p q`) admit a
    deflection that is not parallel to `Sq`. -/
theorem unsigned_equal_area_not_central :
    det (1, 1) (2, 1) = -det (1, 0) (1, 1) ∧
      det (1, 1) (deflection (1, 0) (1, 1) (2, 1)) ≠ 0 := by
  decide

/-- A vertex at S is degenerate: both areas vanish for every next vertex, so the
    area data fix no direction. -/
theorem vertex_at_centre_degenerate (p C : LatticePoint) :
    det (0, 0) C = det p (0, 0) := by
  simp [det]

/-- The sense is not fixed by areas: an outward kick (`+1`) keeps the oriented
    area equal, as does the inward kick (`-1`). -/
theorem outward_kick_equal_area :
    det (1, 1) (kick (1, 1) (extend (1, 0) (1, 1)) 1) = det (1, 0) (1, 1) ∧
      det (1, 1) (kick (1, 1) (extend (1, 0) (1, 1)) (-1)) = det (1, 0) (1, 1) := by
  decide

end NewtonLimitDynamics.Polygon.Converse
