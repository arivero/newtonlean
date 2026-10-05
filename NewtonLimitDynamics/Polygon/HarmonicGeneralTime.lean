import NewtonLimitDynamics.Polygon.GeneralForceTime
import NewtonLimitDynamics.Polygon.HarmonicGeneralEndpoint
import NewtonLimitDynamics.Polygon.HarmonicTimeRealization
import NewtonLimitDynamics.Polygon.PositionValues

/-! Exact harmonic instance of the constructed general time map. All actual
sample bounds are derived on the retained short window. The old harmonic
declarations remain available, and no new historical edge is asserted. -/

namespace NewtonLimitDynamics.Polygon.HarmonicGeneralTime
open NewtonLimitDynamics
open TimeSubdivision PointBounds ForceClasses HarmonicStability HarmonicDyadic
open HarmonicGeneralEndpoint

theorem actual_run_state_bound (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (j k : Nat) (hk : k ≤ blocks j) :
    Fraction.le (stateNorm (BoundedIteration.run (linearField w) (duration T j) s k))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) := by
  rw [run_eq_schedule]
  exact HarmonicTimeRealization.countState_le_two w T s j k hT hs hk

def conditions (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    GeneralForcePrefix.Conditions (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
      (harmonicBound w s) s hE where
  toConditions := HarmonicGeneralEndpoint.conditions w E0 T s hw hE hT hs
theorem harmonic_prefix_eq (b : Nat → Bool) (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (j : Nat) :
    GeneralForcePrefix.prefixState b (harmonicOracle w hw) E0 T s hE j =
      HarmonicBinaryPrefix.prefixState b w T s j := by
  rw [GeneralForcePrefix.prefixState,GeneralForcePrefix.countState,harmonic_field,run_eq_schedule]
  rfl

theorem harmonic_name_equiv (b : Nat → Bool) (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    CauchyValues.NameEquiv
      (GeneralForcePrefix.prefixName b (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
        (harmonicBound w s) s hE (conditions w E0 T s hw hE hT hs))
      (HarmonicBinaryPrefix.prefixName b w T s hT hs) := by
  intro eps heps
  refine ⟨0,fun j _ => ?_⟩
  change Fraction.lt (CauchyValues.distance
    (GeneralForcePrefix.prefixState b (harmonicOracle w hw) E0 T s hE j)
    (HarmonicBinaryPrefix.prefixState b w T s j)) eps
  rw [harmonic_prefix_eq]
  exact CauchyValues.distance_self_lt _ eps heps

theorem harmonic_value_eq (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (x : BinaryTime.BinaryTime T hT) :
    GeneralForceTime.gammaValue (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
      (harmonicBound w s) s hE (conditions w E0 T s hw hE hT hs) x =
      HarmonicTimeRealization.gammaValue w T s hT hs x := by
  induction x using Quotient.inductionOn with
  | _ b => exact Quotient.sound (harmonic_name_equiv b w E0 T s hw hE hT hs)

theorem harmonic_position_eq (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (x : BinaryTime.BinaryTime T hT) :
    GeneralForceTime.gammaPosition (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
      (harmonicBound w s) s hE (conditions w E0 T s hw hE hT hs) x =
      PositionValues.gammaPosition w T s hT hs x := by
  exact congrArg PositionValues.asPosition (harmonic_value_eq w E0 T s hw hE hT hs x)

end NewtonLimitDynamics.Polygon.HarmonicGeneralTime
