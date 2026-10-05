import NewtonLimitDynamics.Polygon.GeneralForcePathRegion
import BarrowLib.Polygon.SquareContentValues

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

theorem D_meshValue_lower_cut (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) (q : Fraction) :
    Below q (D_meshValue o E0 T tau L B s hE d m).val ↔ D_mesh o E0 T tau L B s hE d m q :=
  contentValue_lower_cut _ _ q

theorem D_meshValue_nonnegative (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Below (Fraction.ofInt 0) (D_meshValue o E0 T tau L B s hE d m).val :=
  contentValue_nonnegative _ _

theorem D_meshValue_budget_bound (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Within (D_meshValue o E0 T tau L B s hE d m).val (embed (scalarState (Fraction.ofInt 0)))
      (duration (budgetCoefficient E0 T tau L B s d.calibration_positive) m) :=
  within_mono _ _ _ _ (Fraction.le_of_equiv (actual_budget_geometric o E0 T tau L B s hE d m))
    (contentValue_within_zero _ _)

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

theorem D_meshValue_independent_cover (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat)
    (c : Cover (Region o E0 T tau L B s hE d m)) :
    D_meshValue o E0 T tau L B s hE d m = contentValue (Region o E0 T tau L B s hE d m) c :=
  contentValue_independent_cover _ _ c

theorem D_meshValue_zero_window (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) (hz : T.num=0) :
    (D_meshValue o E0 T tau L B s hE d m).val = embed (scalarState (Fraction.ofInt 0)) := by
  apply (within_zero_iff _ _).mp
  exact within_mono _ _ _ _
    (Fraction.le_of_equiv (budget_zero_window E0 T tau L B s d.calibration_positive m hz))
    (D_meshValue_budget_bound o E0 T tau L B s hE d m)

end NewtonLimitDynamics.Polygon.GeneralForcePathContent
