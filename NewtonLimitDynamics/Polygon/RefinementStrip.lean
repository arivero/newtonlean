import NewtonLimitDynamics.Polygon.Contact

namespace NewtonLimitDynamics.Polygon

/-- Coordinate difference used only for the finite triangle calculation. -/
def latticeSub (p q : LatticePoint) : LatticePoint :=
  (p.1-q.1, p.2-q.2)

/-- The signed doubled area between a coarse edge A-C and a one-cell refined
    polygon A-B-C. It is a closed polygon difference, not a swept sector and
    does not name an actual limiting curve. -/
def refinementStripTwice (a b c : LatticePoint) : Int :=
  det a b + det b c - det a c

/-- Nonnegative size of the finite signed strip. Taking an absolute value does
    not turn cancellation into an enclosure estimate. -/
def refinementDefect (a b c : LatticePoint) : Nat :=
  (refinementStripTwice a b c).natAbs

/-- The closed polygon difference is exactly the doubled area of its triangle.
    This is finite determinant algebra for Euclidean triangle decomposition;
    it uses no integration, derivatives, or limiting curve theorem. -/
theorem refinementStripTwice_eq_triangle (a b c : LatticePoint) :
    refinementStripTwice a b c = det (latticeSub b a) (latticeSub c a) := by
  simp [refinementStripTwice, det, latticeSub, Int.sub_mul, Int.mul_sub]
  have hab₁ : a.1*b.2 = b.2*a.1 := Int.mul_comm _ _
  have hab₂ : a.2*b.1 = b.1*a.2 := Int.mul_comm _ _
  have haa : a.1*a.2 = a.2*a.1 := Int.mul_comm _ _
  omega

theorem det_translation (origin a b : LatticePoint) :
    det (latticeAdd origin a) (latticeAdd origin b) =
      det a b + det origin b - det origin a := by
  simp [det, latticeAdd, Int.add_mul, Int.mul_add]
  have hoo : origin.1*origin.2 = origin.2*origin.1 := Int.mul_comm _ _
  have hao : a.1*origin.2 = origin.2*a.1 := Int.mul_comm _ _
  have hao' : a.2*origin.1 = origin.1*a.2 := Int.mul_comm _ _
  omega

/-- Translating both finite polygons leaves their enclosed signed strip area
    unchanged. -/
theorem refinementStripTwice_translation (origin a b c : LatticePoint) :
    refinementStripTwice (latticeAdd origin a) (latticeAdd origin b)
      (latticeAdd origin c) = refinementStripTwice a b c := by
  simp only [refinementStripTwice, det_translation]
  omega

theorem refinementDefect_eq_zero_iff (a b c : LatticePoint) :
    refinementDefect a b c = 0 ↔ refinementStripTwice a b c = 0 := by
  simp [refinementDefect]

/-- Spatial compatibility for a single coarse cell and a two-cell fine polygon.
    Both sides are finite `motion` data. This condition is deliberately only
    endpoint matching; no common force or time-refinement law has been derived. -/
def oneCellMotionRefinementCompatible
    (coarseStart coarseEnd fineStart fineMiddle : LatticePoint)
    (coarseImpulse fineImpulse : Nat → Int) : Prop :=
  (motion lattice coarseStart coarseEnd coarseImpulse 0).1 =
      (motion lattice fineStart fineMiddle fineImpulse 0).1 ∧
  (motion lattice coarseStart coarseEnd coarseImpulse 0).2 =
      (motion lattice fineStart fineMiddle fineImpulse 1).2

theorem oneCellMotionRefinementCompatible_start
    (coarseStart coarseEnd fineStart fineMiddle : LatticePoint)
    (coarseImpulse fineImpulse : Nat → Int)
    (h : oneCellMotionRefinementCompatible coarseStart coarseEnd fineStart fineMiddle
      coarseImpulse fineImpulse) :
    (motion lattice coarseStart coarseEnd coarseImpulse 0).1 =
      (motion lattice fineStart fineMiddle fineImpulse 0).1 :=
  h.1

theorem oneCellMotionRefinementCompatible_end
    (coarseStart coarseEnd fineStart fineMiddle : LatticePoint)
    (coarseImpulse fineImpulse : Nat → Int)
    (h : oneCellMotionRefinementCompatible coarseStart coarseEnd fineStart fineMiddle
      coarseImpulse fineImpulse) :
    (motion lattice coarseStart coarseEnd coarseImpulse 0).2 =
      (motion lattice fineStart fineMiddle fineImpulse 1).2 :=
  h.2

/-- A nonzero local strip from an actual inward fine impulse and a spatially
    compatible coarse cell. This is not nonuniqueness for one fixed force law. -/
theorem inward_oneCell_refinement_compatible :
    oneCellMotionRefinementCompatible (1, 0) (0, 1) (1, 0) (1, 1)
      (fun _ => 0) inwardOneRadialImpulse := by
  constructor
  · rfl
  · decide

theorem inward_oneCell_refinement_defect :
    refinementDefect (1, 0) (1, 1)
      (motion lattice (1, 0) (1, 1) inwardOneRadialImpulse 1).2 = 1 := by
  decide

end NewtonLimitDynamics.Polygon
