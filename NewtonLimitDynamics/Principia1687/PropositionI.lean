import NewtonLimitDynamics.Polygon.PathDefect

/-!
1687 Proposition I, finite equal-cell reconstruction only. Source:
NATP00077 par44–45,
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45.
The proof explicitly invokes Law I, the laws' Corollary 1, then composes the
equal triangle areas (`componendo`). The construction's two named Euclidean
preservation identities and geometric area semantics are supplied premises.

Unsigned doubled triangle sums count cells with multiplicity. Inward sense,
sector-union interpretation, and the final curve/uninterrupted-force passage
through Lemma III Corollary 4 remain separate. No 1713 premise is imported.

The main defect D_mesh is the nonnegative area BETWEEN polygon and actual
trajectory over the same interval, with endpoint connectors made explicit.
It is not the Kepler sector area in the proposition. The conditional control
below requires that region's enclosure; the finite area law does not supply it.
-/

namespace Principia1687.PropositionI

open NewtonLimitDynamics.Polygon
open NewtonLimitDynamics
open NewtonLimitDynamics.Polygon.PathDefect

variable {Point Impulse : Type}

theorem finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

/-- Finite content of the same-edition `componendo` sentence; positive total
    times are derived, not left implicit in a cross-multiplied identity. -/
theorem finite_componendo (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

/-- Conditional control of the intervening polygon–trajectory region. The
    curve, its relation to the construction, and the enclosure are supplied
    geometric obligations; Lemma III Corollary 4 is not silently discharged. -/
theorem polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry

end Principia1687.PropositionI
