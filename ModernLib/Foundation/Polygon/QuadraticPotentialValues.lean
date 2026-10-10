import ModernLib.Foundation.Polygon.PairingValues
import ModernLib.Foundation.Polygon.QuadraticSecants
import BarrowLib.Polygon.RationalIntervals

/-! Quadratic scalar values and their normalized tangent-continuation
increments. The polynomial remainder is finite algebra, and its Cauchy
completion uses the shared pairing and secant operators. No potential-force
relation or desired leading asymptotic is supplied as a premise. -/

namespace NewtonLimitDynamics.Polygon.QuadraticPotentialValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates HarmonicStability
open HarmonicTimeComparison CauchyValues SecantValues PairingValues BinaryTime HarmonicDyadic PositionValues
open QuadraticSecants

def quadratic (c : Fraction) (p : Point) : Fraction := Fraction.mul c (dot p p)

def quadraticName (c : Fraction) (a : EndpointCauchyName) : EndpointCauchyName :=
  secantName c (pairingName dotForm a a) (constantName (PositionValues.zeroPoint,PositionValues.zeroPoint))

def quadraticValue (c : Fraction) (x : Value) : Value :=
  secantValue c (pairingValue dotForm x x) (embed (PositionValues.zeroPoint,PositionValues.zeroPoint))

-- Modern dependency score: 19/94 (M=19, H=75; transitive project theorems/axioms).
theorem quadraticValue_embed (c : Fraction) (s : Point × Point) :
    quadraticValue c (embed s) = embed (scalarState (quadratic c s.1)) := by
  apply Quotient.sound
  exact nameEquiv_of_levelwise_stateEquiv _ _ (fun j =>
    scaled_pairing_approximant dotForm c (constantName s) (constantName s) j)

def normalizedStep (c h : Fraction) (ht : 0 < h.num) (s u : Point × Point) : Fraction :=
  Fraction.mul (Fraction.mul (TimeCalibration.inverse h ht) (TimeCalibration.inverse h ht))
    (durationDifference (quadratic c (pointAdd s.1 (pointScale h s.2))) (quadratic c u.1))

def normalizedStepName (c h : Fraction) (ht : 0 < h.num) (a b : EndpointCauchyName) : EndpointCauchyName :=
  secantName (Fraction.mul (TimeCalibration.inverse h ht) (TimeCalibration.inverse h ht))
    (quadraticName c b) (quadraticName c (inertialName h a))

def normalizedStepValue (c h : Fraction) (ht : 0 < h.num) (x y : Value) : Value :=
  secantValue (Fraction.mul (TimeCalibration.inverse h ht) (TimeCalibration.inverse h ht))
    (quadraticValue c y) (quadraticValue c (inertialValue h x))

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem normalized_remainder_identity (c h : Fraction) (ht : 0 < h.num)
    (s u : Point × Point) (a : Point) :
    Fraction.equiv (durationDifference (Fraction.mul c (dot a s.1)) (normalizedStep c h ht s u))
      (Fraction.mul c (Fraction.add
        (dot (pointSub (QuadraticSecants.secondState h ht s u).1 a) s.1)
        (Fraction.add (Fraction.mul h (dot (QuadraticSecants.secondState h ht s u).1 s.2))
          (Fraction.mul (Fraction.mul h h).half.half
            (dot (QuadraticSecants.secondState h ht s u).1 (QuadraticSecants.secondState h ht s u).1))))) := by
  simp only [normalizedStep,quadratic,QuadraticSecants.secondState,
    secantState,pointState,velocityState,dot,durationDifference,negF,TimeCalibration.inverse,
    pointSub,pointNeg,pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,
    Fraction.ofInt,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one]
  simp only [show (2 : Int)=1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf <;> omega

-- Modern dependency score: 2/32 (M=2, H=30; transitive project theorems/axioms).
theorem normalized_remainder_bound (c h P V Z D : Fraction) (ht : 0 < h.num)
    (s u : Point × Point) (a : Point)
    (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) (hZ : 0 ≤ Z.num)
    (hp : Fraction.le (pointNorm s.1) P) (hv : Fraction.le (pointNorm s.2) V)
    (hz : Fraction.le (pointNorm (QuadraticSecants.secondState h ht s u).1) Z)
    (hd : Fraction.le (pointDistance (QuadraticSecants.secondState h ht s u).1 a) D) :
    Fraction.le (durationDifference (Fraction.mul c (dot a s.1)) (normalizedStep c h ht s u)).abs
      (Fraction.mul c.abs (Fraction.add (Fraction.mul D P)
        (Fraction.add (Fraction.mul h (Fraction.mul Z V))
          (Fraction.mul (Fraction.mul h h).half.half (Fraction.mul Z Z))))) := by
  let z := (QuadraticSecants.secondState h ht s u).1
  let q := (Fraction.mul h h).half.half
  have hh : 0 ≤ h.num := Int.le_of_lt ht
  have hq : 0 ≤ q.num := Fraction.nonnegative_mul _ _ hh hh
  have h1 := Fraction.magnitudes.le_trans (dot_abs_le_product (pointSub z a) s.1)
    (Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative_left hp (pointDistance z a) (pointNorm_nonnegative _))
      (Fraction.mul_le_mul_nonnegative hd P hP))
  have h2 := Fraction.magnitudes.le_trans (dot_abs_le_product z s.2)
    (Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative_left hv (pointNorm z) (pointNorm_nonnegative _))
      (Fraction.mul_le_mul_nonnegative hz V hV))
  have h3 := Fraction.magnitudes.le_trans (dot_abs_le_product z z)
    (Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative_left hz (pointNorm z) (pointNorm_nonnegative _))
      (Fraction.mul_le_mul_nonnegative hz Z hZ))
  have h2s := Fraction.mul_le_mul_nonnegative_left h2 h hh
  have h3s := Fraction.mul_le_mul_nonnegative_left h3 q hq
  have h2e := Fraction.equiv_trans (Fraction.abs_mul h (dot z s.2))
    (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl _))
  have h3e := Fraction.equiv_trans (Fraction.abs_mul q (dot z z))
    (Fraction.mul_equiv (Fraction.abs_of_nonnegative q hq) (Fraction.equiv_refl _))
  have hinner := Fraction.magnitudes.le_trans (Fraction.abs_add_le (dot (pointSub z a) s.1)
    (Fraction.add (Fraction.mul h (dot z s.2)) (Fraction.mul q (dot z z))))
    (Fraction.add_le_add h1 (Fraction.magnitudes.le_trans (Fraction.abs_add_le _ _)
      (Fraction.add_le_add (Fraction.le_equiv_left h2e h2s) (Fraction.le_equiv_left h3e h3s))))
  have hscaled := Fraction.mul_le_mul_nonnegative_left hinner c.abs (Fraction.abs_num_nonnegative c)
  exact Fraction.le_equiv_left (Fraction.equiv_trans (Fraction.abs_equiv
    (normalized_remainder_identity c h ht s u a)) (Fraction.abs_mul _ _)) hscaled

def remainderCoefficient (c T P V Z U : Fraction) : Fraction :=
  Fraction.mul c.abs (Fraction.add (Fraction.mul P U)
    (Fraction.add (Fraction.mul Z V) (Fraction.mul T.half.half (Fraction.mul Z Z))))

def roundingCoefficient (c P A : Fraction) : Fraction :=
  Fraction.mul c.abs (Fraction.mul P A)

-- Modern dependency score: 0/3 (M=0, H=3; transitive project theorems/axioms).
theorem remainderCoefficient_nonnegative (c T P V Z U : Fraction)
    (hT : 0 ≤ T.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) (hZ : 0 ≤ Z.num) (hU : 0 ≤ U.num) :
    0 ≤ (remainderCoefficient c T P V Z U).num :=
  Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative c)
    (Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hP hU)
      (Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hZ hV)
        (Fraction.nonnegative_mul _ _ hT (Fraction.nonnegative_mul _ _ hZ hZ))))

-- Modern dependency score: 3/34 (M=3, H=31; transitive project theorems/axioms).
theorem uniform_frame_bound (c h T P V Z U r A : Fraction) (ht : 0 < h.num)
    (s u : Point × Point) (a : Point)
    (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) (hZ : 0 ≤ Z.num)
    (hwindow : Fraction.le h T)
    (hp : Fraction.le (pointNorm s.1) P) (hv : Fraction.le (pointNorm s.2) V)
    (hz : Fraction.le (pointNorm (QuadraticSecants.secondState h ht s u).1) Z)
    (hd : Fraction.le (pointDistance (QuadraticSecants.secondState h ht s u).1 a)
      (Fraction.add (Fraction.mul h U) (Fraction.mul r A))) :
    Fraction.le (durationDifference (Fraction.mul c (dot a s.1)) (normalizedStep c h ht s u)).abs
      (Fraction.add (Fraction.mul h (remainderCoefficient c T P V Z U))
        (Fraction.mul r (roundingCoefficient c P A))) := by
  have hb := normalized_remainder_bound c h P V Z _ ht s u a hP hV hZ hp hv hz hd
  have hsq := Fraction.mul_le_mul_nonnegative_left hwindow h (Int.le_of_lt ht)
  have hquarter := RationalIntervals.half_le (RationalIntervals.half_le hsq)
  have hlast := Fraction.mul_le_mul_nonnegative hquarter (Fraction.mul Z Z)
    (Fraction.nonnegative_mul _ _ hZ hZ)
  have htotal := Fraction.mul_le_mul_nonnegative_left
    (Fraction.add_le_add_left (Fraction.add_le_add_left hlast (Fraction.mul h (Fraction.mul Z V)))
      (Fraction.mul (Fraction.add (Fraction.mul h U) (Fraction.mul r A)) P))
    c.abs (Fraction.abs_num_nonnegative c)
  apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans hb htotal)
  simp only [remainderCoefficient,roundingCoefficient,Fraction.equiv,Fraction.add,Fraction.mul,
    Fraction.half,Int.add_mul,Int.mul_add]
  ac_nf

/-- The constructed scalar increment has the expected finite approximant.
This identity connects completed potential values to the polynomial estimate. -/
-- Modern dependency score: 12/77 (M=12, H=65; transitive project theorems/axioms).
theorem normalized_step_approximant (c h : Fraction) (ht : 0 < h.num)
    (a b : EndpointCauchyName) (j : Nat) :
    stateEquiv ((normalizedStepName c h ht a b).approx j)
      (scalarState (normalizedStep c h ht (a.approx j) (b.approx j))) := by
  have hzero : zeroPoint=(Fraction.ofInt 0,Fraction.ofInt 0) := rfl
  have hscalar : ∀ q, scalarState q=((q,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0)) := fun _ => rfl
  constructor
  · constructor <;>
      simp only [normalizedStepName,normalizedStep,quadraticName,quadratic,inertialName,
        secantName,secantState,pointState,pairingName,BinaryLift.name,
        secantOperation,pairingOperation,pairingState,dotForm,hscalar,
        mapName,velocityState,constantName,hzero,
        pointEquiv,pointSub,pointNeg,pointAdd,pointScale,dot,durationDifference,negF,
        Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one,
        Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add,Int.neg_zero] <;>
      ac_nf <;> omega
  · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

end NewtonLimitDynamics.Polygon.QuadraticPotentialValues
