import BarrowLib.Polygon.ConvexCover
import ModernLib.Foundation.Polygon.PositionValues

namespace NewtonLimitDynamics.Polygon.ConvexValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds ConvexCover FiniteEstimates CauchyValues
open HarmonicDyadic

/-- A fixed rational interpolation is Lipschitz in both endpoints. -/
-- Modern dependency score: 0/31 (M=0, H=31; transitive project theorems/axioms).
theorem lerp_distance (a : Fraction) (ha : UnitInterval a)
    (p q p' q' : Point) :
    Fraction.le (pointDistance (lerp a p q) (lerp a p' q'))
      (Fraction.add (pointDistance p p') (pointDistance q q')) := by
  have he : pointEquiv (pointSub (lerp a p q) (lerp a p' q'))
      (pointAdd (pointScale (complement a) (pointSub p p'))
        (pointScale a (pointSub q q'))) := by
    constructor <;>
      simp only [pointEquiv,lerp,pointSub,pointNeg,pointAdd,pointScale,
        Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,
        Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega
  have hca : Fraction.le (complement a) (Fraction.ofInt 1) := by
    simp only [complement,Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul]
    have hnonneg := ha.1
    omega
  have haa : Fraction.le a (Fraction.ofInt 1) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using ha.2
  have hc := Fraction.mul_le_mul_nonnegative hca (pointDistance p p')
    (pointNorm_nonnegative _)
  have hd := Fraction.mul_le_mul_nonnegative haa (pointDistance q q')
    (pointNorm_nonnegative _)
  have hs := Fraction.add_equiv
    (Fraction.equiv_trans (pointNorm_scale (complement a) (pointSub p p'))
      (Fraction.mul_equiv (complement_abs a ha) (Fraction.equiv_refl _)))
    (Fraction.equiv_trans (pointNorm_scale a (pointSub q q'))
      (Fraction.mul_equiv (interval_abs a ha) (Fraction.equiv_refl _)))
  have hb := Fraction.le_equiv_right
    (pointNorm_add_le (pointScale (complement a) (pointSub p p'))
      (pointScale a (pointSub q q'))) hs
  have hlast := Fraction.add_le_add hc hd
  have hone : Fraction.equiv
      (Fraction.add (Fraction.mul (Fraction.ofInt 1) (pointDistance p p'))
        (Fraction.mul (Fraction.ofInt 1) (pointDistance q q')))
      (Fraction.add (pointDistance p p') (pointDistance q q')) := by
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one]
  exact Fraction.magnitudes.le_trans (Fraction.le_equiv_left (pointNorm_equiv he) hb)
    (Fraction.le_equiv_right hlast hone)

def convexState (a : Fraction) (s t : Point × Point) : Point × Point :=
  (lerp a s.1 t.1,PositionValues.zeroPoint)

-- Modern dependency score: 1/36 (M=1, H=35; transitive project theorems/axioms).
theorem convexState_distance (a : Fraction) (ha : UnitInterval a)
    (s t s' t' : Point × Point) :
    Fraction.le (distance (convexState a s t) (convexState a s' t'))
      (Fraction.add (distance s s') (distance t t')) := by
  have he : Fraction.equiv (distance (convexState a s t) (convexState a s' t'))
      (pointDistance (lerp a s.1 t.1) (lerp a s'.1 t'.1)) :=
    Fraction.equiv_trans
      (Fraction.add_equiv (Fraction.equiv_refl _)
        (pointDistance_self_zero PositionValues.zeroPoint)) (Fraction.add_zero _)
  have hs : Fraction.le (pointDistance s.1 s'.1) (distance s s') :=
    Fraction.le_add_nonnegative _ _ (pointNorm_nonnegative _)
  have ht : Fraction.le (pointDistance t.1 t'.1) (distance t t') :=
    Fraction.le_add_nonnegative _ _ (pointNorm_nonnegative _)
  exact Fraction.le_equiv_left he
    (Fraction.magnitudes.le_trans (lerp_distance a ha _ _ _ _) (Fraction.add_le_add hs ht))

def convexName (a : Fraction) (ha : UnitInterval a)
    (s t : EndpointCauchyName) : EndpointCauchyName where
  approx := fun n => convexState a (s.approx n) (t.approx n)
  cauchy := by
    intro eps heps
    have hh := (show 0 < eps.half.num from heps)
    obtain ⟨N,hN⟩ := s.cauchy eps.half hh
    obtain ⟨M,hM⟩ := t.cauchy eps.half hh
    refine ⟨max N M,?_⟩
    intro m n hm hn
    have hs := hN m n (Nat.le_trans (Nat.le_max_left _ _) hm)
      (Nat.le_trans (Nat.le_max_left _ _) hn)
    have ht := hM m n (Nat.le_trans (Nat.le_max_right _ _) hm)
      (Nat.le_trans (Nat.le_max_right _ _) hn)
    have hsum := Fraction.add_lt_add hs ht
    exact Fraction.magnitudes.lt_of_le_lt (convexState_distance a ha _ _ _ _)
      (Fraction.magnitudes.lt_of_lt_le hsum (Fraction.le_of_equiv (Fraction.half_add_self eps)))

-- Modern dependency score: 2/41 (M=2, H=39; transitive project theorems/axioms).
theorem convexName_equiv (a : Fraction) (ha : UnitInterval a)
    (s t s' t' : EndpointCauchyName) (hs : NameEquiv s s') (ht : NameEquiv t t') :
    NameEquiv (convexName a ha s t) (convexName a ha s' t') := by
  intro eps heps
  have hh := (show 0 < eps.half.num from heps)
  obtain ⟨N,hN⟩ := hs eps.half hh
  obtain ⟨M,hM⟩ := ht eps.half hh
  refine ⟨max N M,?_⟩
  intro n hn
  have hsum := Fraction.add_lt_add
    (hN n (Nat.le_trans (Nat.le_max_left _ _) hn))
    (hM n (Nat.le_trans (Nat.le_max_right _ _) hn))
  exact Fraction.magnitudes.lt_of_le_lt (convexState_distance a ha _ _ _ _)
    (Fraction.magnitudes.lt_of_lt_le hsum (Fraction.le_of_equiv (Fraction.half_add_self eps)))

def convexValue (a : Fraction) (ha : UnitInterval a) (x y : Value) : Value :=
  Quotient.liftOn₂ x y (fun s t => realize (convexName a ha s t))
    (fun s t s' t' hs ht => Quotient.sound (convexName_equiv a ha s t s' t' hs ht))

open PositionValues

-- Modern dependency score: 0/39 (M=0, H=39; transitive project theorems/axioms).
theorem convexState_anchor_bound (a : Fraction) (ha : UnitInterval a)
    (s t : Point × Point) (centre : Point) (R : Fraction)
    (hs : Fraction.le (distance s (centre,zeroPoint)) R)
    (ht : Fraction.le (distance t (centre,zeroPoint)) R) :
    Fraction.le (distance (convexState a s t) (centre,zeroPoint)) R := by
  have hp : Fraction.le (pointNorm (pointSub s.1 centre)) R :=
    Fraction.magnitudes.le_trans (Fraction.le_add_nonnegative _ _
      (pointNorm_nonnegative _)) hs
  have hq : Fraction.le (pointNorm (pointSub t.1 centre)) R :=
    Fraction.magnitudes.le_trans (Fraction.le_add_nonnegative _ _
      (pointNorm_nonnegative _)) ht
  have he : Fraction.equiv (distance (convexState a s t) (centre,zeroPoint))
      (pointNorm (pointSub (lerp a s.1 t.1) centre)) :=
    Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _)
      (pointSub_self_zero zeroPoint)) (Fraction.add_zero _)
  exact Fraction.le_equiv_left he (lerp_ball_bound a ha centre _ _ R hp hq)

-- Modern dependency score: 6/52 (M=6, H=46; transitive project theorems/axioms).
theorem convexName_ball (a : Fraction) (ha : UnitInterval a)
    (s t : EndpointCauchyName) (centre : Point) (R : Fraction)
    (hs : NameBound s (constantName (centre,zeroPoint)) R)
    (ht : NameBound t (constantName (centre,zeroPoint)) R) :
    NameBound (convexName a ha s t) (constantName (centre,zeroPoint)) R := by
  intro eps heps
  obtain ⟨N,hN⟩ := hs eps.half heps
  obtain ⟨M,hM⟩ := ht eps.half heps
  refine ⟨max N M,?_⟩
  intro n hn
  have hp := Fraction.magnitudes.lt_implies_le
    (hN n (Nat.le_trans (Nat.le_max_left _ _) hn))
  have hq := Fraction.magnitudes.lt_implies_le
    (hM n (Nat.le_trans (Nat.le_max_right _ _) hn))
  exact Fraction.magnitudes.lt_of_le_lt (convexState_anchor_bound a ha _ _ _ _ hp hq)
    (CauchyValues.add_lt_add_left (Fraction.half_lt eps heps) R)

/-- A common completed centre need not be a rational embedded point. The
finite convex bound is applied to projected approximants of that centre. -/
-- Modern dependency score: 7/51 (M=7, H=44; transitive project theorems/axioms).
theorem convexName_relative_bound (a : Fraction) (ha : UnitInterval a)
    (s t centre : EndpointCauchyName) (R : Fraction)
    (hs : NameBound s centre R) (ht : NameBound t centre R) :
    NameBound (convexName a ha s t)
      (mapName positionState position_nonexpansive centre) R := by
  intro eps heps
  obtain ⟨N,hN⟩ := hs eps.half heps
  obtain ⟨M,hM⟩ := ht eps.half heps
  refine ⟨max N M,?_⟩
  intro n hn
  have hp := Fraction.magnitudes.le_trans
    (position_nonexpansive (s.approx n) (centre.approx n))
    (Fraction.magnitudes.lt_implies_le (hN n (Nat.le_trans (Nat.le_max_left _ _) hn)))
  have hq := Fraction.magnitudes.le_trans
    (position_nonexpansive (t.approx n) (centre.approx n))
    (Fraction.magnitudes.lt_implies_le (hM n (Nat.le_trans (Nat.le_max_right _ _) hn)))
  exact Fraction.magnitudes.lt_of_le_lt
    (convexState_anchor_bound a ha (positionState (s.approx n))
      (positionState (t.approx n)) (centre.approx n).1 _ hp hq)
    (CauchyValues.add_lt_add_left (Fraction.half_lt eps heps) R)

-- Modern dependency score: 24/81 (M=24, H=57; transitive project theorems/axioms).
theorem convexValue_relative_bound (a : Fraction) (ha : UnitInterval a)
    (x y centre : Value) (R : Fraction)
    (hx : Within x centre R) (hy : Within y centre R) :
    Within (convexValue a ha x y) (positionValue centre) R := by
  induction x using Quotient.inductionOn with
  | _ s =>
    induction y using Quotient.inductionOn with
    | _ t =>
      induction centre using Quotient.inductionOn with
      | _ c => exact convexName_relative_bound a ha s t c R hx hy

-- Modern dependency score: 20/77 (M=20, H=57; transitive project theorems/axioms).
theorem convexValue_ball (a : Fraction) (ha : UnitInterval a)
    (x y : Value) (centre : Point) (R : Fraction)
    (hx : Within x (embed (centre,zeroPoint)) R)
    (hy : Within y (embed (centre,zeroPoint)) R) :
    Within (convexValue a ha x y) (embed (centre,zeroPoint)) R := by
  induction x using Quotient.inductionOn with
  | _ s =>
    induction y using Quotient.inductionOn with
    | _ t => exact convexName_ball a ha s t centre R hx hy

-- Modern dependency score: 14/65 (M=14, H=51; transitive project theorems/axioms).
theorem convexValue_position (a : Fraction) (ha : UnitInterval a) (x y : Value) :
    positionValue (convexValue a ha x y) = convexValue a ha x y := by
  induction x using Quotient.inductionOn with
  | _ s =>
    induction y using Quotient.inductionOn with
    | _ t => rfl

def convexPosition (a : Fraction) (ha : UnitInterval a)
    (x y : PositionValue) : PositionValue :=
  ⟨convexValue a ha x.val y.val,convexValue_position a ha x.val y.val⟩

-- Modern dependency score: 0/11 (M=0, H=11; transitive project theorems/axioms).
theorem first_convex_state (a : Fraction) (s t : Point × Point) :
    stateEquiv (firstState (convexState a s t))
      (convexState a (firstState s) (firstState t)) := by
  constructor
  · constructor
    · exact Fraction.equiv_refl _
    · change Fraction.equiv (Fraction.ofInt 0)
        (Fraction.add (Fraction.mul (complement a) (Fraction.ofInt 0))
          (Fraction.mul a (Fraction.ofInt 0)))
      exact Fraction.equiv_symm (Fraction.equiv_trans
        (Fraction.add_equiv (Fraction.mul_zero _) (Fraction.mul_zero _))
        (Fraction.add_zero _))
  · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

-- Modern dependency score: 0/11 (M=0, H=11; transitive project theorems/axioms).
theorem second_convex_state (a : Fraction) (s t : Point × Point) :
    stateEquiv (secondState (convexState a s t))
      (convexState a (secondState s) (secondState t)) := by
  constructor
  · constructor
    · change Fraction.equiv (Fraction.ofInt 0)
        (Fraction.add (Fraction.mul (complement a) (Fraction.ofInt 0))
          (Fraction.mul a (Fraction.ofInt 0)))
      exact Fraction.equiv_symm (Fraction.equiv_trans
        (Fraction.add_equiv (Fraction.mul_zero _) (Fraction.mul_zero _))
        (Fraction.add_zero _))
    · exact Fraction.equiv_refl _
  · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

-- Modern dependency score: 16/75 (M=16, H=59; transitive project theorems/axioms).
theorem firstValue_convex (a : Fraction) (ha : UnitInterval a) (x y : Value) :
    firstValue (convexValue a ha x y) =
      convexValue a ha (firstValue x) (firstValue y) := by
  induction x using Quotient.inductionOn with
  | _ s =>
    induction y using Quotient.inductionOn with
    | _ t =>
      apply Quotient.sound
      exact nameEquiv_of_levelwise_stateEquiv _ _ (fun n => first_convex_state a _ _)

-- Modern dependency score: 16/75 (M=16, H=59; transitive project theorems/axioms).
theorem secondValue_convex (a : Fraction) (ha : UnitInterval a) (x y : Value) :
    secondValue (convexValue a ha x y) =
      convexValue a ha (secondValue x) (secondValue y) := by
  induction x using Quotient.inductionOn with
  | _ s =>
    induction y using Quotient.inductionOn with
    | _ t =>
      apply Quotient.sound
      exact nameEquiv_of_levelwise_stateEquiv _ _ (fun n => second_convex_state a _ _)

-- Modern dependency score: 35/99 (M=35, H=64; transitive project theorems/axioms).
theorem convexPosition_square (a : Fraction) (ha : UnitInterval a)
    (x y : PositionValue) (centre : Point) (R : NonnegativeRadius)
    (hx : CoordinateSquare centre R x) (hy : CoordinateSquare centre R y) :
    CoordinateSquare centre R (convexPosition a ha x y) := by
  constructor
  · change Within (firstValue (convexValue a ha x.val y.val)) _ _
    rw [firstValue_convex]
    exact convexValue_ball a ha _ _ (firstState (centre,zeroPoint)).1 R.val hx.1 hy.1
  · change Within (secondValue (convexValue a ha x.val y.val)) _ _
    rw [secondValue_convex]
    exact convexValue_ball a ha _ _ (secondState (centre,zeroPoint)).1 R.val hx.2 hy.2

-- Modern dependency score: 15/73 (M=15, H=58; transitive project theorems/axioms).
theorem convexValue_zero (ha : UnitInterval (Fraction.ofInt 0)) (x y : Value) :
    convexValue (Fraction.ofInt 0) ha x y = positionValue x := by
  induction x using Quotient.inductionOn with
  | _ s =>
    induction y using Quotient.inductionOn with
    | _ t =>
      apply Quotient.sound
      exact nameEquiv_of_levelwise_stateEquiv _ _ (fun n =>
        ⟨lerp_zero (s.approx n).1 (t.approx n).1,
          ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩)

-- Modern dependency score: 15/73 (M=15, H=58; transitive project theorems/axioms).
theorem convexValue_one (ha : UnitInterval (Fraction.ofInt 1)) (x y : Value) :
    convexValue (Fraction.ofInt 1) ha x y = positionValue y := by
  induction x using Quotient.inductionOn with
  | _ s =>
    induction y using Quotient.inductionOn with
    | _ t =>
      apply Quotient.sound
      exact nameEquiv_of_levelwise_stateEquiv _ _ (fun n =>
        ⟨lerp_one (s.approx n).1 (t.approx n).1,
          ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩)

-- Modern dependency score: 17/75 (M=17, H=58; transitive project theorems/axioms).
theorem convexPosition_zero (ha : UnitInterval (Fraction.ofInt 0))
    (x y : PositionValue) : convexPosition (Fraction.ofInt 0) ha x y = x := by
  apply Subtype.ext
  exact (convexValue_zero ha x.val y.val).trans x.property

-- Modern dependency score: 17/75 (M=17, H=58; transitive project theorems/axioms).
theorem convexPosition_one (ha : UnitInterval (Fraction.ofInt 1))
    (x y : PositionValue) : convexPosition (Fraction.ofInt 1) ha x y = y := by
  apply Subtype.ext
  exact (convexValue_one ha x.val y.val).trans y.property

-- Modern dependency score: 11/70 (M=11, H=59; transitive project theorems/axioms).
theorem convexValue_swap (a : Fraction) (ha : UnitInterval a) (x y : Value) :
    convexValue a ha x y = convexValue (complement a) (complement_interval a ha) y x := by
  induction x using Quotient.inductionOn with
  | _ s =>
    induction y using Quotient.inductionOn with
    | _ t =>
      apply Quotient.sound
      exact nameEquiv_of_levelwise_stateEquiv _ _ (fun n =>
        ⟨lerp_swap a (s.approx n).1 (t.approx n).1,
          ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩)

-- Modern dependency score: 17/76 (M=17, H=59; transitive project theorems/axioms).
theorem convexPosition_swap (a : Fraction) (ha : UnitInterval a)
    (x y : PositionValue) :
    convexPosition a ha x y = convexPosition (complement a) (complement_interval a ha) y x :=
  Subtype.ext (convexValue_swap a ha x.val y.val)

end NewtonLimitDynamics.Polygon.ConvexValues
