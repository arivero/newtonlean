import BarrowLib.Polygon.PairingValues
import BarrowLib.Polygon.QuadraticSecants

/-! The signed doubled triangle of a completed point, its tangent continuation
and an actual next completed point. Shared pairings and secants construct it;
finite algebra identifies its H^-3 normalization with half the determinant of
velocity and normalized second departure. It is not an unsigned lobe or area
of a matched region. -/

namespace NewtonLimitDynamics.Polygon.TangentTriangleValues
open NewtonLimitDynamics
open TimeSubdivision HarmonicStability PointBounds HarmonicDyadic CauchyValues
open PositionValues SecantValues PairingValues BinaryTime QuadraticSecants

def triangleValue (h : Fraction) (x y : Value) : Value :=
  pairingValue detForm (secantValue (Fraction.ofInt 1) (inertialValue h x) x)
    (secantValue (Fraction.ofInt 1) y (inertialValue h x))

def normalizedTriangleValue (h : Fraction) (ht : 0 < h.num) (x y : Value) : Value :=
  let q := TimeCalibration.inverse h ht
  secantValue (Fraction.mul q (Fraction.mul q q)) (triangleValue h x y) (embed (zeroPoint,zeroPoint))

theorem triangleValue_embed (h : Fraction) (s u : Point × Point) :
    triangleValue h (embed s) (embed u) =
      embed (scalarState (TriangleBounds.triangleTwice s.1 (pointAdd s.1 (pointScale h s.2)) u.1)) := by
  apply Quotient.sound
  apply nameEquiv_of_levelwise_stateEquiv
  intro j
  have hzero : zeroPoint=(Fraction.ofInt 0,Fraction.ofInt 0) := rfl
  have hscalar : ∀ q, scalarState q=((q,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0)) := fun _ => rfl
  constructor
  · constructor <;>
      simp only [triangleValue,inertialValue,inertialName,secantName,secantState,pointState,
        velocityValue,mapValue,mapName,velocityState,pairingName,pairingState,detForm,det,
        TriangleBounds.triangleTwice,constantName,hscalar,hzero,pointEquiv,pointSub,pointNeg,
        pointAdd,pointScale,negF,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one,
        Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add,Int.neg_zero] <;>
      ac_nf <;> omega
  · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

/-- Exact completed identity for the signed doubled tangent-deflection
triangle. The next point is arbitrary; no curve expansion is assumed. -/
theorem normalized_triangle_identity (h : Fraction) (ht : 0 < h.num) (x y : Value) :
    normalizedTriangleValue h ht x y =
      secantValue (Fraction.ofInt 1).half
        (pairingValue detForm (velocityValue x) (QuadraticSecants.secondValue h ht x y)) (embed (zeroPoint,zeroPoint)) := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      apply Quotient.sound
      apply nameEquiv_of_levelwise_stateEquiv
      intro j
      have hzero : zeroPoint=(Fraction.ofInt 0,Fraction.ofInt 0) := rfl
      have hscalar : ∀ q, scalarState q=((q,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0)) := fun _ => rfl
      constructor
      · constructor <;>
          simp only [normalizedTriangleValue,triangleValue,inertialValue,inertialName,QuadraticSecants.secondValue,
            velocityValue,mapValue,mapName,velocityState,secantName,secantState,pointState,
            pairingName,pairingState,detForm,det,constantName,hscalar,hzero,TimeCalibration.inverse,
            pointEquiv,pointSub,pointNeg,pointAdd,pointScale,negF,Fraction.equiv,Fraction.add,
            Fraction.mul,Fraction.half,Fraction.ofInt,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,
            Int.one_mul,Int.mul_one,Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add,Int.neg_zero] <;>
          ac_nf <;> omega
      · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

end NewtonLimitDynamics.Polygon.TangentTriangleValues
