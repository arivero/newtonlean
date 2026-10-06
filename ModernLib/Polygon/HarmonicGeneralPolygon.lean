import ModernLib.Polygon.GeneralForcePolygonCurve
import ModernLib.Polygon.HarmonicPolygonCurve
import ModernLib.Polygon.HarmonicGeneralEndpoint

/-! Exact equality of the general sampled polygon instance and the retained
harmonic polygon map. It requires no curve or small-window premise. -/

namespace NewtonLimitDynamics.Polygon.HarmonicGeneralPolygon
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix HarmonicStability ForceClasses
open CauchyValues PositionValues

theorem harmonic_polygonMap_eq (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (m : Nat)
    (t : BinaryTime.BinaryTime T hT) :
    GeneralForcePolygonCurve.polygonMap (harmonicOracle w hw) E0 T s hE hT m t =
      HarmonicPolygonCurve.polygonMap w T s hT m t := by
  induction t using Quotient.inductionOn with
  | _ b =>
    apply Subtype.ext
    change positionValue (realize (PolygonValues.polygonName b T hT m
      (GeneralForcePolygonCurve.vertices (harmonicOracle w hw) E0 T s hE m))) =
      positionValue (realize (HarmonicPolygonCurve.polygonName b w T s hT m))
    apply congrArg positionValue
    apply Quotient.sound
    apply nameEquiv_of_levelwise_stateEquiv
    intro j
    have hp : GeneralForcePrefix.countState (harmonicOracle w hw) E0 T s hE m (ticks b m) =
        prefixState b w T s m := by
      rw [GeneralForcePrefix.countState,HarmonicGeneralEndpoint.harmonic_field,run_eq_schedule]
      rfl
    change stateEquiv
      (AffineValues.affineState
        (GeneralForcePrefix.countState (harmonicOracle w hw) E0 T s hE m (ticks b m)).1
        (GeneralForcePrefix.countState (harmonicOracle w hw) E0 T s hE m (ticks b m)).2 _)
      (AffineValues.affineState (prefixState b w T s m).1 (prefixState b w T s m).2 _)
    rw [hp]
    exact ⟨⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

end NewtonLimitDynamics.Polygon.HarmonicGeneralPolygon
