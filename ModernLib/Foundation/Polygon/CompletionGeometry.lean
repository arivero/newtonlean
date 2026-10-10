import ModernLib.Foundation.Polygon.ConvexValues
import ModernLib.Foundation.Polygon.ScaledTolerance
import BarrowLib.Common.RationalExhaustion

/-! Elementary closure and closed coordinate enclosures in the explicit Cauchy
plane. Closure uses all positive rational tolerances; no external topology,
measure, integral or curve is a premise. -/
namespace NewtonLimitDynamics.Polygon.CompletionGeometry
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic CauchyValues PositionValues
open HarmonicTimeRealization

/-- Closed bounds can be exhausted from arbitrarily small rational enlargements. -/
-- Modern dependency score: 15/52 (M=15, H=37; transitive project theorems/axioms).
theorem within_of_thickenings (x y : Value) (R : Fraction)
    (h : ∀ eps : Fraction, 0 < eps.num → Within x y (Fraction.add R eps)) :
    Within x y R := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      intro eps heps
      obtain ⟨N,hN⟩ := h eps.half heps eps.half heps
      refine ⟨N,fun n hn => ?_⟩
      exact lt_equiv_right (hN n hn) (Fraction.equiv_trans
        (Fraction.add_assoc R eps.half eps.half)
        (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.half_add_self eps)))

/-- Rational closed distance bounds are exact after completion. -/
-- Modern dependency score: 18/62 (M=18, H=44; transitive project theorems/axioms).
theorem within_embedded_iff (a b : Point × Point) (R : Fraction) :
    Within (embed a) (embed b) R ↔ Fraction.le (distance a b) R := by
  constructor
  · intro h
    apply (Fraction.le_iff_toRat _ _).mpr
    apply Rational.le_of_enlargements
    intro epsR hepsR
    let eps := Fraction.ofRat epsR
    have heps : 0 < eps.num := (Fraction.positive_iff_toRat eps).mpr
      (by simpa only [eps, Fraction.toRat_ofRat] using hepsR)
    rw [← Fraction.toRat_ofRat epsR, ← Fraction.toRat_add]
    apply (Fraction.le_iff_toRat _ _).mp
    change Fraction.le _ (Fraction.add _ eps)
    obtain ⟨N,hN⟩ := h eps heps
    exact Fraction.magnitudes.lt_implies_le (hN N (Nat.le_refl _))
  · intro h
    exact nameBound_of_eventual_le _ _ R 0 (fun _ _ => h)

/-- Exact closed bounds for finite points embedded in the completed plane. -/
-- Modern dependency score: 24/71 (M=24, H=47; transitive project theorems/axioms).
theorem within_embedPosition_iff (p q : Point) (R : Fraction) :
    Within (embedPosition p).val (embedPosition q).val R ↔
      Fraction.le (FiniteEstimates.pointDistance p q) R := by
  change Within (embed (p,zeroPoint)) (embed (q,zeroPoint)) R ↔ _
  have he : Fraction.equiv (distance (p,zeroPoint) (q,zeroPoint))
      (FiniteEstimates.pointDistance p q) :=
    Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _)
      (FiniteEstimates.pointDistance_self_zero zeroPoint)) (Fraction.add_zero _)
  exact ⟨fun h => Fraction.le_equiv_left (Fraction.equiv_symm he)
      ((within_embedded_iff _ _ _).mp h),
    fun h => (within_embedded_iff _ _ _).mpr (Fraction.le_equiv_left he h)⟩

/-- The coordinate length of a position is its distance from the origin. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem position_distance_zero (s : Point × Point) :
    Fraction.equiv (distance (positionState s) (zeroPoint,zeroPoint)) (pointNorm s.1) := by
  change Fraction.equiv
    (distance (s.1,(Fraction.ofInt 0,Fraction.ofInt 0))
      ((Fraction.ofInt 0,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0)))
    (pointNorm s.1)
  simp only [distance,HarmonicComparison.stateSub,pointSub,
    pointAdd,pointNeg,stateNorm,pointNorm,Fraction.equiv,Fraction.add,Fraction.abs,Fraction.ofInt,
    Int.zero_mul,Int.mul_zero,Int.add_zero,Int.natAbs_zero,Int.ofNat_zero,Int.neg_zero,
    Int.mul_one,Int.one_mul]

/-- A finite coordinate band is closed under Cauchy realization. The inner
bound excludes every smaller closed ball, without adding a completed norm. -/
-- Modern dependency score: 23/69 (M=23, H=46; transitive project theorems/axioms).
theorem position_band_realize (a : EndpointCauchyName) (r R : Fraction)
    (h : ∀ n, Fraction.le r (pointNorm (a.approx n).1) ∧
      Fraction.le (pointNorm (a.approx n).1) R) :
    Within (positionValue (realize a)) (embed (zeroPoint,zeroPoint)) R ∧
      ∀ D, Within (positionValue (realize a)) (embed (zeroPoint,zeroPoint)) D →
        Fraction.le r D := by
  constructor
  · exact nameBound_of_eventual_le
      (mapName positionState position_nonexpansive a) (constantName (zeroPoint,zeroPoint)) R 0
      (fun n _ => Fraction.le_equiv_left (position_distance_zero _) (h n).2)
  · intro D hD
    apply (Fraction.le_iff_toRat _ _).mpr
    apply Rational.le_of_enlargements
    intro epsR hepsR
    let eps := Fraction.ofRat epsR
    have heps : 0 < eps.num := (Fraction.positive_iff_toRat eps).mpr
      (by simpa only [eps, Fraction.toRat_ofRat] using hepsR)
    rw [← Fraction.toRat_ofRat epsR, ← Fraction.toRat_add]
    apply (Fraction.le_iff_toRat _ _).mp
    change Fraction.le _ (Fraction.add _ eps)
    obtain ⟨N,hN⟩ := hD eps heps
    have hd := Fraction.le_equiv_left (Fraction.equiv_symm (position_distance_zero (a.approx N)))
      (Fraction.magnitudes.lt_implies_le (hN N (Nat.le_refl _)))
    exact Fraction.magnitudes.le_trans (h N).1 hd

def Closure (A : PositionValue → Prop) (x : PositionValue) : Prop :=
  ∀ eps : Fraction, 0 < eps.num →
    ∃ y : PositionValue, A y ∧ Within x.val y.val eps

-- Modern dependency score: 23/63 (M=23, H=40; transitive project theorems/axioms).
theorem closure_contains (A : PositionValue → Prop) (x : PositionValue)
    (hx : A x) : Closure A x := by
  intro eps heps
  refine ⟨x,hx,?_⟩
  exact within_mono _ _ _ _
    (Fraction.magnitudes.lt_implies_le ((Fraction.positive_iff_zero_lt eps).mp heps))
    ((within_zero_iff _ _).mpr rfl)

-- Modern dependency score: 19/58 (M=19, H=39; transitive project theorems/axioms).
theorem closure_mono (A B : PositionValue → Prop)
    (h : ∀ x, A x → B x) (x : PositionValue) (hx : Closure A x) :
    Closure B x := by
  intro eps heps
  obtain ⟨y,hy,hxy⟩ := hx eps heps
  exact ⟨y,h y hy,hxy⟩

-- Modern dependency score: 27/67 (M=27, H=40; transitive project theorems/axioms).
theorem closure_idempotent (A : PositionValue → Prop) (x : PositionValue) :
    Closure (Closure A) x ↔ Closure A x := by
  constructor
  · intro hx eps heps
    obtain ⟨y,hy,hxy⟩ := hx eps.half heps
    obtain ⟨z,hz,hyz⟩ := hy eps.half heps
    exact ⟨z,hz,within_mono _ _ _ _
      (Fraction.le_of_equiv (Fraction.half_add_self eps))
      (within_triangle _ _ _ _ _ hxy hyz)⟩
  · intro hx
    exact closure_contains (Closure A) x hx

-- Modern dependency score: 25/64 (M=25, H=39; transitive project theorems/axioms).
theorem closure_image_bound (A : PositionValue → Prop) (x : PositionValue)
    (hx : Closure A x) (f : Value → Value)
    (hf : ∀ u v R, Within u v R → Within (f u) (f v) R)
    (centre : Value) (R : Fraction)
    (hA : ∀ y, A y → Within (f y.val) centre R) :
    Within (f x.val) centre R := by
  apply within_of_thickenings
  intro eps heps
  obtain ⟨y,hy,hxy⟩ := hx eps heps
  exact within_mono _ _ _ _ (Fraction.le_of_equiv (Fraction.add_comm eps R))
    (within_triangle _ _ _ _ _ (hf _ _ _ hxy) (hA y hy))

-- Modern dependency score: 34/73 (M=34, H=39; transitive project theorems/axioms).
theorem closure_square (A : PositionValue → Prop) (x : PositionValue)
    (hx : Closure A x) (centre : Point) (R : NonnegativeRadius)
    (hA : ∀ y, A y → CoordinateSquare centre R y) :
    CoordinateSquare centre R x := by
  constructor
  · exact closure_image_bound A x hx firstValue firstValue_within _ R.val
      (fun y hy => (hA y hy).1)
  · exact closure_image_bound A x hx secondValue secondValue_within _ R.val
      (fun y hy => (hA y hy).2)

-- Modern dependency score: 27/66 (M=27, H=39; transitive project theorems/axioms).
theorem square_of_ball_bound (x : PositionValue) (centre : Point)
    (R : NonnegativeRadius) (h : Within x.val (embed (centre,zeroPoint)) R.val) :
    CoordinateSquare centre R x :=
  ⟨firstValue_within _ _ _ h,secondValue_within _ _ _ h⟩

end NewtonLimitDynamics.Polygon.CompletionGeometry
