import ModernLib.Polygon.GeneralForceQuadraticSecants
import ModernLib.Polygon.HarmonicCompletedForce

/-! The retained harmonic curve inherits the constructed normalized
second-order position departure criterion, with all sample bounds derived. -/

namespace NewtonLimitDynamics.Polygon.HarmonicQuadraticSecants
open NewtonLimitDynamics
open TimeSubdivision HarmonicDyadic HarmonicBinaryPrefix ForceClasses CauchyValues DyadicNodes

-- Modern dependency score: 281/488 (M=281, H=207; transitive project theorems/axioms).
theorem second_secants_converge (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (ht : 0 < T.num) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ b : Nat → Bool,
      Within (QuadraticSecants.secondValue (duration T m) ht
        (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m (ticks b m)))
        (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m (ticks b m+1))))
        (HarmonicCompletedForce.linearValue w
          (HarmonicTimeRealization.gammaValue w T s hT hs (Quotient.mk _ b))) eps := by
  obtain ⟨N,hN⟩ := GeneralForceQuadraticSecants.dyadic_second_uniform_identification
    (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
    (HarmonicGeneralEndpoint.harmonicBound w s) s hE
    (HarmonicGeneralTime.conditions w E0 T s hw hE hT hs) ht eps heps
  refine ⟨N,fun m hm b => ?_⟩
  have h := hN m hm b
  rw [GeneralForceQuadraticSecants.cellSecondSecant,HarmonicGeneralTime.harmonic_value_eq,
    HarmonicGeneralTime.harmonic_value_eq,HarmonicCompletedForce.completed_linear_force,
    HarmonicGeneralTime.harmonic_value_eq] at h
  exact h

end NewtonLimitDynamics.Polygon.HarmonicQuadraticSecants
