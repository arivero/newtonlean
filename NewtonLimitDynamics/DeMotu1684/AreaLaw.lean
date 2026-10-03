import NewtonLimitDynamics.Polygon.PathDefect

/-!
Finite reconstruction of De Motu **Theorem 1**, not a retrospectively numbered
Principia proposition. Witness NATP00089 par8–9 (De motu corporum in gyrum,
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par9) and
witness NATP00090 par16–17 (De motu sphæricorum corporum in fluidis,
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17)
remain separate. Both explicitly construct equal-time central-impulse polygons
and say that equal areas are described in equal times. The arbitrary-block
comparison below is a derived finite reconstruction; these passages do not
contain the printed editions' explicit `componendo` sentence.

The shared kernel assumes two named Euclidean preservation identities and
supplied area semantics. It constructs finite vertices and sums unsigned
doubled triangle areas with multiplicity. It does not enforce inward impulses,
identify a sector union, or prove the final `numero infinita et infinitè parva`
passage to uninterrupted force. NATP00089's changing marginal hypothesis/lemma
labels are not silently resolved using NATP00090 or a later edition.

The principal remaining area is D_mesh BETWEEN the polygon and actual
trajectory over one common time interval, with endpoint connectors stated if
needed. It is not the radius-swept Kepler area in Theorem 1. The defect-control
theorems below name the supplied geometric enclosure and vanishing budget;
neither follows from the finite equal-area theorem and neither creates a curve.
-/

namespace DeMotu1684.AreaLaw

open NewtonLimitDynamics.Polygon
open NewtonLimitDynamics
open NewtonLimitDynamics.Polygon.PathDefect

variable {Point Impulse : Type}

/-- NATP00089 par9: finite equal areas, conditional on the named construction
    premises. No limiting conclusion or reconstructed marginal citation. -/
theorem natp00089_finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

/-- NATP00090 par17: separately named witness-local finite equal-area result. -/
theorem natp00090_finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

/-- Derived block comparison from NATP00089's finite equal-area construction.
    Positive time cell and counts rule out division by zero total times. -/
theorem natp00089_finite_block_comparison (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

/-- Derived comparison for NATP00090 alone; it imports no printed-edition
    limiting lemma or premise from NATP00089's unresolved revision layer. -/
theorem natp00090_finite_block_comparison (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

/-- NATP00089's polygon-to-motion obligation, as a conditional reconstruction:
    D_mesh is the nonnegative polygon–trajectory region, NOT its Kepler area.
    No numbered limiting lemma is imported into this witness. -/
theorem natp00089_polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry

/-- Separately named NATP00090 obligation with the same explicit geometric
    premises; its final infinitely-small-triangle assertion remains unproved. -/
theorem natp00090_polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry

end DeMotu1684.AreaLaw
