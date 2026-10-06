import NewtonLimitDynamics

/-! Interface and separation controls for the changed primary convention.
These use the existing general construction and pre-existing finite
counterexample; no independent force example is added. -/
namespace TrajectoryPostulateControls
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision BinaryTime PositionValues SweptArea

example (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    Proportional T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)
      (CentralSchedule.momentum s) :=
  GeneralForceArea.proportional_swept_area o E0 T tau L B s hE d

-- A is a proved law about a given curve; a common swept area exists.
example (T ell : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue)
    (hlaw : Proportional T hT curve ell)
    (t₀ t₁ u₀ u₁ : BinaryTime T hT)
    (ht : intervalElapsedValue T hT t₀ t₁ = intervalElapsedValue T hT u₀ u₁) :
    ∃ area, AreaBetween T hT curve t₀ t₁ area ∧
      AreaBetween T hT curve u₀ u₁ area :=
  proportional_equal_times T hT curve ell hlaw t₀ t₁ u₀ u₁ ht

-- Equal swept sums do not annihilate the between-path patch budget.
example :
    PathDefect.coarseKeplerUnsigned PathDefect.exampleCoarse 2 =
      PathDefect.fineKeplerUnsigned PathDefect.exampleCoarse PathDefect.exampleInserted 2 ∧
    0 < PathDefect.absolutePatchBudget PathDefect.exampleCoarse PathDefect.exampleInserted 2 := by
  have h := PathDefect.equal_Kepler_areas_positive_path_defect
  constructor
  · exact h.2.2.1.trans h.2.2.2.1.symm
  · rw [h.2.2.2.2.2]
    decide

#print axioms SweptArea.proportional_equal_times
#print axioms GeneralForceArea.proportional_swept_area
end TrajectoryPostulateControls
