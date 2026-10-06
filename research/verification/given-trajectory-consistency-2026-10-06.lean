import NewtonLimitDynamics

namespace GivenTrajectoryConsistencyControls
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision CauchyValues BinaryTime PositionValues SweptArea

-- A supplied state curve and separate consistency evidence suffice; the
-- coefficient is computed from its initial data, never an area-law premise.
example (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime T d.time_nonnegative → Value)
    (c : GivenTrajectoryArea.Consistency o E0 T tau L B s hE d u)
    (t₀ t₁ u₀ u₁ : BinaryTime T d.time_nonnegative)
    (ht : intervalElapsedValue T d.time_nonnegative t₀ t₁ =
      intervalElapsedValue T d.time_nonnegative u₀ u₁) :
    ∃ area, SweptArea.AreaBetween T d.time_nonnegative (fun t => asPosition (u t)) t₀ t₁ area ∧
      SweptArea.AreaBetween T d.time_nonnegative (fun t => asPosition (u t)) u₀ u₁ area :=
  SweptArea.proportional_equal_times T d.time_nonnegative _ (CentralSchedule.momentum s)
    (GivenTrajectoryArea.proportional_swept_area o E0 T tau L B s hE d u c)
    t₀ t₁ u₀ u₁ ht

-- The local residual cannot be discarded when the oracle discrepancy is zero.
example : Fraction.equiv
    (GivenMotionComparison.errorBudget (Fraction.ofInt 1) (by decide)
      (Fraction.ofInt 1) (Fraction.ofInt 0) (Fraction.ofInt 1) 1)
    (Fraction.ofInt 4) := by decide

#print axioms TimeCalibration.run_sample_distance_le_source
#print axioms TimeCalibration.run_sample_distance_le_two
#print axioms GivenMotionComparison.count_sample_stateDistance_le_budget
#print axioms GivenTrajectoryArea.equals_constructed
#print axioms GivenTrajectoryArea.proportional_swept_area
#print axioms GivenTrajectoryArea.between_path_content_tends_zero
end GivenTrajectoryConsistencyControls
