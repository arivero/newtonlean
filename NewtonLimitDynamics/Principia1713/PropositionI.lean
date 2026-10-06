import NewtonLimitDynamics.Polygon.PathDefect
import NewtonLimitDynamics.Polygon.GeneralForceArea

/-!
1713 Proposition I, finite equal-cell reconstruction and a separately named modern local curve law. Source:
NATP00082 par50–51,
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51.
The proof invokes this edition's Law I and laws' Corollary 1 and explicitly
composes equal triangle areas. The same mathematical kernel is reusable, but
the historical source and theorem namespace remain 1713-local.

The two named Euclidean identities and area semantics are supplied. Sums of
unsigned doubled triangle areas count repeated coverage. Inward dynamics,
sector identification, Lemma III Corollary 4's curve passage, and uninterrupted
force are not concluded. No 1687 mechanical or limiting premise is imported.

The main D_mesh is the nonnegative area BETWEEN polygon and actual trajectory
over one common time interval, including stated endpoint connectors. It is
separate from the Kepler sector area. The defect-control theorem names the
supplied geometric enclosure; no sector-area identity proves that premise.
-/

namespace Principia1713.PropositionI

open NewtonLimitDynamics.Polygon
open NewtonLimitDynamics
open NewtonLimitDynamics.Polygon.PathDefect

variable {Point Impulse : Type}

theorem finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

/-- This edition's finite `componendo` consequence, before its limiting clause. -/
theorem finite_componendo (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

/-- This edition's conditional polygon–trajectory defect interface. A realized
    trajectory and its geometric enclosure are premises, not conclusions of
    the exact finite Kepler triangle law. -/
theorem polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry

/-- Modern local reconstruction of NATP00082 par51,
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51.
Actual unsigned curve-fan area is proportional to time, counting multiplicity,
and the constructed intervening content vanishes without an enclosure premise.
Planarity is part of the model. Regional Lipschitz/window data are modern
premises; this does not certify the historical continuously acting force
passage or import the 1687 proof as a historical premise. -/
theorem constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t

/-- 1713 Proposition I: modern reconstruction of this edition's componendo step.
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51.
Actual curve-node interval fans give |ell|*|t1-t0|/2, with derived vanishing
intervening content. Planarity is built into the model, swept multiplicity
is counted, and regional Lipschitz/window data remain modern premises.
The source invokes the Laws' Corollary 1 and Lemma III Corollary 4; their historical proofs are separate obligations. No other witness supplies a premise. -/
theorem constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁

end Principia1713.PropositionI
