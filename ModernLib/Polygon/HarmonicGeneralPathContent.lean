import ModernLib.Polygon.GeneralForcePathContent
import ModernLib.Polygon.HarmonicPathContent
import ModernLib.Polygon.HarmonicGeneralPolygon
import ModernLib.Polygon.HarmonicGeneralTime

/-! The actual general harmonic matched region equals the retained region.
Their scalar contents agree despite different proved cover coefficients. -/

namespace NewtonLimitDynamics.Polygon.HarmonicGeneralPathContent
open NewtonLimitDynamics
open TimeSubdivision HarmonicDyadic ForceClasses HarmonicGeneralEndpoint HarmonicGeneralTime
open PositionValues SquareContentValues

-- Modern dependency score: 238/434 (M=238, H=196; transitive project theorems/axioms).
theorem harmonic_region_eq (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (m : Nat) (x : PositionValue) :
    GeneralForcePathRegion.Region (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
      (harmonicBound w s) s hE (conditions w E0 T s hw hE hT hs) m x ↔
      HarmonicPathRegion.Region w T s hT hs m x := by
  have hp := funext (fun t : BinaryTime.BinaryTime T hT =>
    HarmonicGeneralPolygon.harmonic_polygonMap_eq w E0 T s hw hE hT m t)
  have hg := funext (fun t : BinaryTime.BinaryTime T hT =>
    harmonic_position_eq w E0 T s hw hE hT hs t)
  change MatchedRegion.Region T hT _ _ m x ↔ MatchedRegion.Region T hT _ _ m x
  rw [hp,hg]

-- Modern dependency score: 302/511 (M=302, H=209; transitive project theorems/axioms).
theorem harmonic_content_eq (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) :
    GeneralForcePathContent.D_meshValue (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
      (harmonicBound w s) s hE (conditions w E0 T s hw hE hT hs) m =
      HarmonicPathContent.D_meshValue w T s hT hs m :=
  contentValue_region_congr _ _ (harmonic_region_eq w E0 T s hw hE hT hs m) _ _

end NewtonLimitDynamics.Polygon.HarmonicGeneralPathContent
