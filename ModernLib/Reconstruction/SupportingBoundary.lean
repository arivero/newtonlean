import ModernLib.Foundation.Polygon.SupportingBoundary

/-! Cross-result Corollaries III-IV boundary reconstruction; witness models remain distinct. -/

namespace ModernLib.Reconstruction.Principia1687.LemmaIIICorollaries
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision PositionValues BinaryTime HarmonicDyadic DyadicNodes CurveTrace

-- Modern dependency score: 79/181 (M=79, H=102; transitive project theorems/axioms).
theorem corollary3_4_supporting_boundary_reconstruction (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f)
    (points : Nat → Nat → Point)
    (cells : ∀ m k, SupportingTangents.Cell (points m k) (points m (k+1)))
    (hpoints : ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      ∀ k, k≤blocks m → CauchyValues.Within (embedPosition (points m k)).val
        (f (nodeTime T hT m k)).val eps) :
    BoundaryLimit (fun m => SupportingBoundary.supportingTrace (points m) (cells m) (blocks m))
      (ImageTrace f) :=
  SupportingBoundary.dyadic_supportingTrace_limit T hT f hf points cells hpoints

end ModernLib.Reconstruction.Principia1687.LemmaIIICorollaries

namespace ModernLib.Reconstruction.Principia1713.LemmaIIICorollaries
open NewtonLimitDynamics NewtonLimitDynamics.Polygon
open TimeSubdivision PositionValues BinaryTime HarmonicDyadic DyadicNodes CurveTrace

-- Modern dependency score: 79/181 (M=79, H=102; transitive project theorems/axioms).
theorem corollary3_4_supporting_boundary_reconstruction (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f)
    (points : Nat → Nat → Point)
    (cells : ∀ m k, SupportingTangents.Cell (points m k) (points m (k+1)))
    (hpoints : ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      ∀ k, k≤blocks m → CauchyValues.Within (embedPosition (points m k)).val
        (f (nodeTime T hT m k)).val eps) :
    BoundaryLimit (fun m => SupportingBoundary.supportingTrace (points m) (cells m) (blocks m))
      (ImageTrace f) :=
  SupportingBoundary.dyadic_supportingTrace_limit T hT f hf points cells hpoints

end ModernLib.Reconstruction.Principia1713.LemmaIIICorollaries
