import ModernLib.Polygon.GeneralForcePathRegion
import ModernLib.Foundation.Polygon.SquareContentValues
import ModernLib.Polygon.PathDefect

/-! Canonical Cauchy scalar outer content of the actual general matched
polygon/curve region. The all-cover cut, enclosure and geometric decay are
derived; the choice of initial cover affects no completed content value. -/

namespace NewtonLimitDynamics.Polygon.GeneralForcePathContent
open NewtonLimitDynamics
open TimeSubdivision HarmonicDyadic HarmonicTimeRealization CauchyValues PositionValues BinaryTime
open ScalarOrder SquareOuterContent SquareContentValues GeneralForcePathRegion

noncomputable def D_meshValue (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) : ScalarValue :=
  contentValue (Region o E0 T tau L B s hE d m) (actualCover o E0 T tau L B s hE d m)

-- Modern dependency score: 166/365 (M=166, H=199; transitive project theorems/axioms).
theorem D_meshValue_lower_cut (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) (q : Fraction) :
    Below q (D_meshValue o E0 T tau L B s hE d m).val ↔ D_mesh o E0 T tau L B s hE d m q :=
  contentValue_lower_cut _ _ q

-- Modern dependency score: 167/366 (M=167, H=199; transitive project theorems/axioms).
theorem D_meshValue_nonnegative (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Below (Fraction.ofInt 0) (D_meshValue o E0 T tau L B s hE d m).val :=
  contentValue_nonnegative _ _

-- Modern dependency score: 167/368 (M=167, H=201; transitive project theorems/axioms).
theorem D_meshValue_budget_bound (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Within (D_meshValue o E0 T tau L B s hE d m).val (embed (scalarState (Fraction.ofInt 0)))
      (duration (budgetCoefficient E0 T tau L B s d.calibration_positive) m) :=
  within_mono _ _ _ _ (Fraction.le_of_equiv (actual_budget_geometric o E0 T tau L B s hE d m))
    (contentValue_within_zero _ _)

-- Modern dependency score: 169/371 (M=169, H=202; transitive project theorems/axioms).
theorem D_meshValue_tends_zero (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N, ∀ m, N≤m →
      Within (D_meshValue o E0 T tau L B s hE d m).val (embed (scalarState (Fraction.ofInt 0))) eps := by
  obtain ⟨N,hN⟩ := duration_eventually_small
    (budgetCoefficient E0 T tau L B s d.calibration_positive) eps
    (budgetCoefficient_nonnegative E0 T tau L B s hE d.time_nonnegative d.calibration_positive
      d.lipschitz.1 d.bound_nonnegative) heps
  exact ⟨N,fun m hm => within_mono _ _ _ _
    (Fraction.magnitudes.lt_implies_le (hN m hm)) (D_meshValue_budget_bound o E0 T tau L B s hE d m)⟩

/-- The old limiting enclosure is grounded by the constructed curve's actual
nonnegative between-path content. No geometric enclosure is a hypothesis. -/
-- Modern dependency score: 179/381 (M=179, H=202; transitive project theorems/axioms).
theorem polygon_trajectory_enclosure (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    PathDefect.PolygonTrajectoryEnclosure
      (fun mesh => D_meshValue o E0 T tau L B s hE d (RationalEnclosure.level mesh))
      (fun mesh => Fraction.mul mesh (budgetCoefficient E0 T tau L B s d.calibration_positive)) :=
  PathDefect.geometric_sequence_enclosure _ _
    (budgetCoefficient_nonnegative E0 T tau L B s hE d.time_nonnegative d.calibration_positive
      d.lipschitz.1 d.bound_nonnegative)
    (D_meshValue_nonnegative o E0 T tau L B s hE d)
    (D_meshValue_budget_bound o E0 T tau L B s hE d)

/-- Strict rational-neighborhood vanishing of the actual completed content,
using its derived enclosure and an explicit vanishing rational budget. -/
-- Modern dependency score: 183/386 (M=183, H=203; transitive project theorems/axioms).
theorem polygon_trajectory_defect_vanishes (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    Vanishes (fun mesh => D_meshValue o E0 T tau L B s hE d (RationalEnclosure.level mesh)) :=
  PathDefect.polygon_trajectory_defect_vanishes _ _
    (linear_budget_vanishes _ (budgetCoefficient_nonnegative E0 T tau L B s hE d.time_nonnegative
      d.calibration_positive d.lipschitz.1 d.bound_nonnegative))
    (polygon_trajectory_enclosure o E0 T tau L B s hE d)

-- Modern dependency score: 165/364 (M=165, H=199; transitive project theorems/axioms).
theorem D_meshValue_independent_cover (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat)
    (c : Cover (Region o E0 T tau L B s hE d m)) :
    D_meshValue o E0 T tau L B s hE d m = contentValue (Region o E0 T tau L B s hE d m) c :=
  contentValue_independent_cover _ _ c

-- Modern dependency score: 171/372 (M=171, H=201; transitive project theorems/axioms).
theorem D_meshValue_zero_window (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) (hz : T.num=0) :
    (D_meshValue o E0 T tau L B s hE d m).val = embed (scalarState (Fraction.ofInt 0)) := by
  apply (within_zero_iff _ _).mp
  exact within_mono _ _ _ _
    (Fraction.le_of_equiv (budget_zero_window E0 T tau L B s d.calibration_positive m hz))
    (D_meshValue_budget_bound o E0 T tau L B s hE d m)

end NewtonLimitDynamics.Polygon.GeneralForcePathContent
