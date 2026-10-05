import BarrowLib.Polygon.PairingValues
import BarrowLib.Polygon.ScalarOrder
import BarrowLib.Polygon.PolygonFanArea

/-! Triangle fans of completed positions. Every operation uses the shared
one- or two-input Cauchy lift. The vertices are the supplied completed points;
the fan is not defined by a force law or a desired area coefficient. -/

namespace NewtonLimitDynamics.Polygon.FanValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates HarmonicDyadic HarmonicTimeComparison
open HarmonicTimeRealization CauchyValues BinaryTime PositionValues PairingValues ScalarOrder
open SecantValues
open HarmonicAccumulation

def sumState (s t : Point × Point) : Point × Point :=
  scalarState (Fraction.add s.1.1 t.1.1)

theorem sum_state_bound (s t u v : Point × Point) :
    Fraction.le (distance (sumState s t) (sumState u v))
      (Fraction.add (distance s u) (distance t v)) := by
  have he : Fraction.equiv
      (durationDifference (Fraction.add u.1.1 v.1.1) (Fraction.add s.1.1 t.1.1))
      (Fraction.add (durationDifference u.1.1 s.1.1) (durationDifference v.1.1 t.1.1)) := by
    simp only [durationDifference,HarmonicStability.negF,Fraction.equiv,Fraction.add,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf <;> omega
  have hb := Fraction.magnitudes.le_trans (Fraction.abs_add_le _ _)
    (Fraction.add_le_add (first_coordinate_gap s u) (first_coordinate_gap t v))
  exact Fraction.le_equiv_left
    (Fraction.equiv_trans (scalarState_distance _ _) (Fraction.abs_equiv he)) hb

def sumOperation : BinaryLift.Operation where
  apply := sumState
  coefficient := fun _ => Fraction.ofInt 1
  coefficient_nonnegative := fun _ _ => by decide
  distance_bound := by
    intro R hR s t u v hu ht
    apply Fraction.le_equiv_right (sum_state_bound s t u v)
    simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.mul_one]

def sumName (a b : EndpointCauchyName) : EndpointCauchyName :=
  BinaryLift.name sumOperation a b

def sumValue (x y : Value) : Value := BinaryLift.value sumOperation x y

theorem sumValue_realize (a b : EndpointCauchyName) :
    sumValue (realize a) (realize b) = realize (sumName a b) := rfl

theorem sumValue_scalar (x y : Value) : firstValue (sumValue x y) = sumValue x y := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => rfl

def absoluteState (s : Point × Point) : Point × Point := scalarState s.1.1.abs

theorem absolute_nonexpansive (s t : Point × Point) :
    Fraction.le (distance (absoluteState s) (absoluteState t)) (distance s t) :=
  Fraction.le_equiv_left (scalarState_distance _ _)
    (Fraction.magnitudes.le_trans (PolygonFanArea.duration_abs_reverse _ _)
      (first_coordinate_gap s t))

def absoluteName (a : EndpointCauchyName) : EndpointCauchyName :=
  mapName absoluteState absolute_nonexpansive a

def absoluteValue (x : Value) : Value := mapValue absoluteState absolute_nonexpansive x

def sumNames (a : Nat → EndpointCauchyName) : Nat → EndpointCauchyName
  | 0 => constantName (scalarState (Fraction.ofInt 0))
  | n+1 => sumName (sumNames a n) (a n)

def sumValues (a : Nat → Value) : Nat → Value
  | 0 => embed (scalarState (Fraction.ofInt 0))
  | n+1 => sumValue (sumValues a n) (a n)

theorem sumValues_realize (a : Nat → EndpointCauchyName) (n : Nat) :
    sumValues (fun i => realize (a i)) n = realize (sumNames a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sumValue (sumValues (fun i => realize (a i)) n) (realize (a n)) = _
    rw [ih]
    rfl

theorem sumNames_approx (a : Nat → EndpointCauchyName) (n j : Nat) :
    (sumNames a n).approx j =
      scalarState (PolygonFanArea.sum (fun i => (a i).approx j |>.1.1) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change scalarState (Fraction.add ((sumNames a n).approx j).1.1 (a n |>.approx j |>.1.1)) = _
    rw [ih]
    rfl

/-- `unsigned=true` sums individual triangle magnitudes, retaining repeated
coverage with multiplicity. `false` gives the oriented fan. Both are doubled. -/
def fanName (unsigned : Bool) (p : Nat → EndpointCauchyName) (n : Nat) : EndpointCauchyName :=
  sumNames (fun i => if unsigned then absoluteName (pairingName detForm (p i) (p (i+1)))
    else pairingName detForm (p i) (p (i+1))) n

def fanValue (unsigned : Bool) (p : Nat → Value) (n : Nat) : Value :=
  sumValues (fun i => if unsigned then absoluteValue (pairingValue detForm (p i) (p (i+1)))
    else pairingValue detForm (p i) (p (i+1))) n

def finiteFan (unsigned : Bool) (p : Nat → Point) (n : Nat) : Fraction :=
  if unsigned then PolygonFanArea.unsignedFan p n else PolygonFanArea.fan p n

theorem fanValue_realize (unsigned : Bool) (p : Nat → EndpointCauchyName) (n : Nat) :
    fanValue unsigned (fun i => realize (p i)) n = realize (fanName unsigned p n) := by
  cases unsigned <;> exact sumValues_realize _ _

/-- Triangle fans use positions only, irrespective of other state data. -/
theorem fanValue_positions (unsigned : Bool) (p : Nat → Value) (n : Nat) :
    fanValue unsigned (fun i => positionValue (p i)) n = fanValue unsigned p n := by
  have hp : ∀ i, pairingValue detForm (positionValue (p i)) (positionValue (p (i+1))) =
      pairingValue detForm (p i) (p (i+1)) := by
    intro i
    induction p i using Quotient.inductionOn with
    | _ a =>
      induction p (i+1) using Quotient.inductionOn with
      | _ b => rfl
  have hf := funext (fun i => congrArg (fun x => if unsigned then absoluteValue x else x) (hp i))
  unfold fanValue
  rw [hf]

theorem fanName_approx (unsigned : Bool) (p : Nat → EndpointCauchyName) (n j : Nat) :
    (fanName unsigned p n).approx j = scalarState (finiteFan unsigned (fun i => (p i).approx j |>.1) n) := by
  cases unsigned <;> exact sumNames_approx _ _ _

def zeroState : Point × Point := scalarState (Fraction.ofInt 0)

def halfState (s : Point × Point) : Point × Point :=
  secantState (Fraction.ofInt 1).half s zeroState

theorem half_nonexpansive (s t : Point × Point) :
    Fraction.le (distance (halfState s) (halfState t)) (distance s t) := by
  have hb := secant_distance_bound (Fraction.ofInt 1).half s zeroState t zeroState
  have hz := stateSub_self_norm_zero zeroState
  have he : Fraction.equiv
      (Fraction.mul (Fraction.ofInt 1).half.abs (Fraction.add (distance s t) (distance zeroState zeroState)))
      (Fraction.mul (Fraction.ofInt 1).half.abs (distance s t)) := Fraction.equiv_trans
    (Fraction.mul_equiv (Fraction.equiv_refl _) (Fraction.add_equiv (Fraction.equiv_refl _) hz))
    (Fraction.mul_equiv (Fraction.equiv_refl _) (Fraction.add_zero _))
  have hhalf : Fraction.le (Fraction.ofInt 1).half.abs (Fraction.ofInt 1) := by
    unfold Fraction.le
    decide
  have hm := Fraction.mul_le_mul_nonnegative hhalf (distance s t) (stateNorm_nonnegative _)
  have hone : Fraction.equiv (Fraction.mul (Fraction.ofInt 1) (distance s t)) (distance s t) := by
    simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul]
  exact Fraction.magnitudes.le_trans (Fraction.le_equiv_right hb he) (Fraction.le_equiv_right hm hone)

def halfName (a : EndpointCauchyName) : EndpointCauchyName :=
  mapName halfState half_nonexpansive a

def halfValue (x : Value) : Value := mapValue halfState half_nonexpansive x

theorem halfValue_realize (a : EndpointCauchyName) : halfValue (realize a) = realize (halfName a) := rfl

theorem halfValue_within (x y : Value) (R : Fraction) (h : Within x y R) :
    Within (halfValue x) (halfValue y) R := mapValue_within halfState half_nonexpansive x y R h

theorem half_scalar_product (c t : Fraction) :
    stateEquiv (halfState (scalarState (Fraction.mul t c)))
      (secantState c.half (scalarState t) zeroState) := by
  have hzero : zeroPoint=(Fraction.ofInt 0,Fraction.ofInt 0) := rfl
  have hscalar : ∀ q,scalarState q=((q,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0)) := fun _ => rfl
  constructor
  · constructor <;>
      simp only [halfState,zeroState,secantState,pointState,pointSub,pointNeg,pointAdd,pointScale,
        hscalar,hzero,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,Fraction.ofInt,
        Int.zero_mul,Int.mul_zero,Int.neg_zero,Int.zero_add,Int.add_zero,Int.one_mul,Int.mul_one]
      <;> ac_nf
  · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

end NewtonLimitDynamics.Polygon.FanValues
