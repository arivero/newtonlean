import ModernLib.Foundation.Polygon.PairingValues
import ModernLib.Foundation.Polygon.ScalarOrder
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

-- Modern dependency score: 5/23 (M=5, H=18; transitive project theorems/axioms).
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

-- Modern dependency score: 17/70 (M=17, H=53; transitive project theorems/axioms).
theorem sumValue_realize (a b : EndpointCauchyName) :
    sumValue (realize a) (realize b) = realize (sumName a b) := rfl

-- Modern dependency score: 18/71 (M=18, H=53; transitive project theorems/axioms).
theorem sumValue_scalar (x y : Value) : firstValue (sumValue x y) = sumValue x y := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => rfl

def absoluteState (s : Point × Point) : Point × Point := scalarState s.1.1.abs

-- Modern dependency score: 5/17 (M=5, H=12; transitive project theorems/axioms).
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

-- Modern dependency score: 17/70 (M=17, H=53; transitive project theorems/axioms).
theorem sumValues_realize (a : Nat → EndpointCauchyName) (n : Nat) :
    sumValues (fun i => realize (a i)) n = realize (sumNames a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sumValue (sumValues (fun i => realize (a i)) n) (realize (a n)) = _
    rw [ih]
    rfl

-- Modern dependency score: 11/54 (M=11, H=43; transitive project theorems/axioms).
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

/-- A fan over the cells `lo, ..., lo+count-1`, retaining their actual nodes. -/
def intervalName (unsigned : Bool) (p : Nat → EndpointCauchyName)
    (lo count : Nat) : EndpointCauchyName := fanName unsigned (fun i => p (lo+i)) count

def intervalValue (unsigned : Bool) (p : Nat → Value)
    (lo count : Nat) : Value := fanValue unsigned (fun i => p (lo+i)) count

-- Modern dependency score: 22/85 (M=22, H=63; transitive project theorems/axioms).
theorem fanValue_realize (unsigned : Bool) (p : Nat → EndpointCauchyName) (n : Nat) :
    fanValue unsigned (fun i => realize (p i)) n = realize (fanName unsigned p n) := by
  cases unsigned <;> exact sumValues_realize _ _

/-- Triangle fans use positions only, irrespective of other state data. -/
-- Modern dependency score: 23/86 (M=23, H=63; transitive project theorems/axioms).
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

-- Modern dependency score: 24/87 (M=24, H=63; transitive project theorems/axioms).
theorem intervalValue_positions (unsigned : Bool) (p : Nat → Value)
    (lo count : Nat) :
    intervalValue unsigned (fun i => positionValue (p i)) lo count =
      intervalValue unsigned p lo count :=
  fanValue_positions unsigned (fun i => p (lo+i)) count

-- Modern dependency score: 15/73 (M=15, H=58; transitive project theorems/axioms).
theorem fanName_approx (unsigned : Bool) (p : Nat → EndpointCauchyName) (n j : Nat) :
    (fanName unsigned p n).approx j = scalarState (finiteFan unsigned (fun i => (p i).approx j |>.1) n) := by
  cases unsigned <;> exact sumNames_approx _ _ _

-- Modern dependency score: 23/86 (M=23, H=63; transitive project theorems/axioms).
theorem intervalValue_realize (unsigned : Bool) (p : Nat → EndpointCauchyName)
    (lo count : Nat) :
    intervalValue unsigned (fun i => realize (p i)) lo count =
      realize (intervalName unsigned p lo count) :=
  fanValue_realize unsigned (fun i => p (lo+i)) count

-- Modern dependency score: 16/74 (M=16, H=58; transitive project theorems/axioms).
theorem intervalName_approx (unsigned : Bool) (p : Nat → EndpointCauchyName)
    (lo count j : Nat) :
    (intervalName unsigned p lo count).approx j =
      scalarState (PolygonFanArea.intervalFan unsigned
        (fun i => (p i).approx j |>.1) lo count) := by
  cases unsigned <;>
    simp only [intervalName,fanName_approx,PolygonFanArea.intervalFan,
      PolygonFanArea.intervalSum,finiteFan,PolygonFanArea.unsignedFan,
      PolygonFanArea.fan,Nat.add_assoc,Bool.false_eq_true,ite_false,ite_true]

def zeroState : Point × Point := scalarState (Fraction.ofInt 0)

/-- Adjacent blocks of actual completed triangle fans compose by addition. -/
-- Modern dependency score: 29/100 (M=29, H=71; transitive project theorems/axioms).
theorem intervalValue_compose (unsigned : Bool) (p : Nat → Value) (lo n k : Nat) :
    intervalValue unsigned p lo (n+k) =
      sumValue (intervalValue unsigned p lo n) (intervalValue unsigned p (lo+n) k) := by
  classical
  let names := fun i => Classical.choose (Quotient.exists_rep (p i))
  have hp : (fun i => realize (names i)) = p :=
    funext (fun i => Classical.choose_spec (Quotient.exists_rep (p i)))
  rw [← hp,intervalValue_realize,intervalValue_realize,intervalValue_realize,sumValue_realize]
  apply Quotient.sound
  apply nameEquiv_of_levelwise_stateEquiv
  intro j
  change stateEquiv ((intervalName unsigned names lo (n+k)).approx j)
    (sumState ((intervalName unsigned names lo n).approx j)
      ((intervalName unsigned names (lo+n) k).approx j))
  rw [intervalName_approx,intervalName_approx,intervalName_approx]
  let pts := fun i => ((names i).approx j).1
  change stateEquiv (scalarState (PolygonFanArea.intervalFan unsigned pts lo (n+k)))
    (scalarState (Fraction.add (PolygonFanArea.intervalFan unsigned pts lo n)
      (PolygonFanArea.intervalFan unsigned pts (lo+n) k)))
  exact ⟨⟨PolygonFanArea.intervalFan_compose unsigned pts lo n k,Fraction.equiv_refl _⟩,
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

def halfState (s : Point × Point) : Point × Point :=
  secantState (Fraction.ofInt 1).half s zeroState

-- Modern dependency score: 2/46 (M=2, H=44; transitive project theorems/axioms).
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

-- Modern dependency score: 11/64 (M=11, H=53; transitive project theorems/axioms).
theorem halfValue_realize (a : EndpointCauchyName) : halfValue (realize a) = realize (halfName a) := rfl

-- Modern dependency score: 21/76 (M=21, H=55; transitive project theorems/axioms).
theorem halfValue_within (x y : Value) (R : Fraction) (h : Within x y R) :
    Within (halfValue x) (halfValue y) R := mapValue_within halfState half_nonexpansive x y R h

-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
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
