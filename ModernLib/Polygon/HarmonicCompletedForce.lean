import ModernLib.Polygon.CompletedForce
import ModernLib.Polygon.HarmonicGeneralTime
import ModernLib.Foundation.Polygon.SecantValues

/-! The general completed force specializes to the retained linear central
law at all completed positions, and its actual polygon force samples converge
uniformly along the retained harmonic curve. -/

namespace NewtonLimitDynamics.Polygon.HarmonicCompletedForce
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic HarmonicBinaryPrefix
open HarmonicStability ForceClasses CauchyValues SecantValues PositionValues

def linearValue (w : Fraction) (x : Value) : Value :=
  secantValue (negF w) x (embed (zeroPoint,zeroPoint))

theorem completed_linear_force (w E0 : Fraction) (hw : 0 ≤ w.num) (hE : 0 < E0.num)
    (hL : LipschitzOn (harmonicOracle w hw).toOracle w.abs)
    (x : Value) (hx : SampledValues.Admissible (fun q => (harmonicOracle w hw).region q.1) x) :
    CompletedForce.forceValue (harmonicOracle w hw) E0 w.abs hE
      hL x hx = linearValue w x := by
  obtain ⟨a,rfl,ha⟩ := hx
  rw [CompletedForce.forceValue_realize (harmonicOracle w hw) E0 w.abs hE hL a ha]
  ·
    apply Quotient.sound
    apply nameEquiv_of_levelwise_stateEquiv
    intro j
    exact ⟨pointScale_congr (negF w) (pointEquiv_symm (pointSub_zero (a.approx j).1)),
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

theorem retained_curve_force_samples_converge (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j, N ≤ j → ∀ b : Nat → Bool,
      Within (embed (accelerationState (linearField w (prefixState b w T s j).1)))
        (linearValue w (HarmonicTimeRealization.gammaValue w T s hT hs (Quotient.mk _ b))) eps := by
  obtain ⟨N,hN⟩ := CompletedForce.prefix_force_uniform_convergence (harmonicOracle w hw)
    E0 T (Fraction.ofInt 1) w.abs (HarmonicGeneralEndpoint.harmonicBound w s) s hE
    (HarmonicGeneralTime.conditions w E0 T s hw hE hT hs) eps heps
  refine ⟨N,fun j hj b => ?_⟩
  have h := hN j hj b
  rw [completed_linear_force] at h
  rw [HarmonicGeneralTime.harmonic_value_eq,
    HarmonicGeneralTime.harmonic_prefix_eq,HarmonicGeneralEndpoint.harmonic_field] at h
  exact h

end NewtonLimitDynamics.Polygon.HarmonicCompletedForce
