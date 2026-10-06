import ModernLib.Polygon.GeneralForceAccelerationSecants
import ModernLib.Polygon.HarmonicCompletedForce

/-! The retained harmonic curve's completed velocity secants converge to
its completed linear central force, as an instance of the general result. -/

namespace NewtonLimitDynamics.Polygon.HarmonicAccelerationSecants
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix HarmonicStability ForceClasses
open CauchyValues SecantValues DyadicNodes

def cellAccelerationSecant (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (ht : 0 < T.num) (m k : Nat) : Value :=
  secantValue (TimeCalibration.inverse (duration T m) ht)
    (velocityValue (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m (k+1))))
    (velocityValue (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m k)))

theorem cellAccelerationSecant_eq (w E0 T : Fraction) (s : Point × Point) (hw : 0 ≤ w.num)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (ht : 0 < T.num) (m k : Nat) :
    GeneralForceAccelerationSecants.cellAccelerationSecant (harmonicOracle w hw)
      E0 T (Fraction.ofInt 1) w.abs (HarmonicGeneralEndpoint.harmonicBound w s) s hE
      (HarmonicGeneralTime.conditions w E0 T s hw hE hT hs) ht m k =
      cellAccelerationSecant w T s hT hs ht m k := by
  rw [GeneralForceAccelerationSecants.cellAccelerationSecant,cellAccelerationSecant,
    HarmonicGeneralTime.harmonic_value_eq,HarmonicGeneralTime.harmonic_value_eq]

theorem acceleration_secants_converge (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (ht : 0 < T.num) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ b : Nat → Bool,
      Within (cellAccelerationSecant w T s hT hs ht m (ticks b m))
        (HarmonicCompletedForce.linearValue w
          (HarmonicTimeRealization.gammaValue w T s hT hs (Quotient.mk _ b))) eps := by
  obtain ⟨N,hN⟩ := GeneralForceAccelerationSecants.dyadic_acceleration_uniform_identification
    (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
    (HarmonicGeneralEndpoint.harmonicBound w s) s hE
    (HarmonicGeneralTime.conditions w E0 T s hw hE hT hs) ht eps heps
  refine ⟨N,fun m hm b => ?_⟩
  have h := hN m hm b
  rw [cellAccelerationSecant_eq,HarmonicCompletedForce.completed_linear_force,
    HarmonicGeneralTime.harmonic_value_eq] at h
  exact h

end NewtonLimitDynamics.Polygon.HarmonicAccelerationSecants
