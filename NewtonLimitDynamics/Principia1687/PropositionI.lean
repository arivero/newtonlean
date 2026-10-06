import NewtonLimitDynamics.Polygon.PathDefect
import NewtonLimitDynamics.Polygon.GeneralForceArea

/-!
1687 Proposition I: finite equal-cell reconstruction and a separately named
modern local constructed-curve area law. Source:
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

/-- Modern local reconstruction of NATP00077 par45,
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45.
Actual curve-fan area is proportional to time and the actual intervening
content vanishes; neither is supplied as a premise. The model is planar.
Regional Lipschitz sampling and a calibrated short window are modern premises,
not a proof of the historical Lemma III Corollary 4 invocation. No 1713 premise. -/
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

/-- 1687 Proposition I: modern reconstruction of the explicit componendo step.
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45.
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

end Principia1687.PropositionI
