import ModernLib.Polygon.GeneralForceSecants
import ModernLib.Polygon.HarmonicGeneralTime

/-! The retained harmonic curve's position-secants result is a corollary
of the actual general central-force construction. No derivative primitive
or new historical dependency is used. -/

namespace NewtonLimitDynamics.Polygon.HarmonicSecants
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix HarmonicStability ForceClasses
open CauchyValues SecantValues DyadicNodes

def cellSecant (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (ht : 0 < T.num) (m k : Nat) : Value :=
  secantValue (TimeCalibration.inverse (duration T m) ht)
    (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m (k+1)))
    (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m k))

theorem cellSecant_eq (w E0 T : Fraction) (s : Point × Point) (hw : 0 ≤ w.num)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (ht : 0 < T.num) (m k : Nat) :
    GeneralForceSecants.cellSecant (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
      (HarmonicGeneralEndpoint.harmonicBound w s) s hE
      (HarmonicGeneralTime.conditions w E0 T s hw hE hT hs) ht m k =
      cellSecant w T s hT hs ht m k := by
  rw [GeneralForceSecants.cellSecant,cellSecant,
    HarmonicGeneralTime.harmonic_value_eq,HarmonicGeneralTime.harmonic_value_eq]

theorem velocity_secants_converge (w E0 T : Fraction) (s : Point × Point) (hw : 0 ≤ w.num)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (ht : 0 < T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ b : Nat → Bool,
      Within (cellSecant w T s hT hs ht m (ticks b m))
        (velocityValue (HarmonicTimeRealization.gammaValue w T s hT hs (Quotient.mk _ b))) eps := by
  obtain ⟨N,hN⟩ := GeneralForceSecants.dyadic_velocity_uniform_identification (harmonicOracle w hw)
    E0 T (Fraction.ofInt 1) w.abs (HarmonicGeneralEndpoint.harmonicBound w s) s hE
    (HarmonicGeneralTime.conditions w E0 T s hw hE hT hs) ht eps heps
  refine ⟨N,fun m hm b => ?_⟩
  have h := hN m hm b
  rw [cellSecant_eq,HarmonicGeneralTime.harmonic_value_eq] at h
  exact h

end NewtonLimitDynamics.Polygon.HarmonicSecants
