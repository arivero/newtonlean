import BarrowLib.Polygon.ConvexValues
import BarrowLib.Polygon.ScaledTolerance
import BarrowLib.Common.RationalExhaustion

/-! Elementary closure and closed coordinate enclosures in the explicit Cauchy
plane. Closure uses all positive rational tolerances; no external topology,
measure, integral or curve is a premise. -/
namespace NewtonLimitDynamics.Polygon.CompletionGeometry
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic CauchyValues PositionValues
open HarmonicTimeRealization

/-- Closed bounds can be exhausted from arbitrarily small rational enlargements. -/
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
theorem within_embedded_iff (a b : Point × Point) (R : Fraction) :
    Within (embed a) (embed b) R ↔ Fraction.le (distance a b) R := by
  constructor
  · intro h
    apply Fraction.le_of_enlargements
    intro eps heps
    obtain ⟨N,hN⟩ := h eps heps
    exact Fraction.magnitudes.lt_implies_le (hN N (Nat.le_refl _))
  · intro h
    exact nameBound_of_eventual_le _ _ R 0 (fun _ _ => h)

def Closure (A : PositionValue → Prop) (x : PositionValue) : Prop :=
  ∀ eps : Fraction, 0 < eps.num →
    ∃ y : PositionValue, A y ∧ Within x.val y.val eps

theorem closure_contains (A : PositionValue → Prop) (x : PositionValue)
    (hx : A x) : Closure A x := by
  intro eps heps
  refine ⟨x,hx,?_⟩
  exact within_mono _ _ _ _
    (Fraction.magnitudes.lt_implies_le ((Fraction.positive_iff_zero_lt eps).mp heps))
    ((within_zero_iff _ _).mpr rfl)

theorem closure_mono (A B : PositionValue → Prop)
    (h : ∀ x, A x → B x) (x : PositionValue) (hx : Closure A x) :
    Closure B x := by
  intro eps heps
  obtain ⟨y,hy,hxy⟩ := hx eps heps
  exact ⟨y,h y hy,hxy⟩

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

theorem closure_square (A : PositionValue → Prop) (x : PositionValue)
    (hx : Closure A x) (centre : Point) (R : NonnegativeRadius)
    (hA : ∀ y, A y → CoordinateSquare centre R y) :
    CoordinateSquare centre R x := by
  constructor
  · exact closure_image_bound A x hx firstValue firstValue_within _ R.val
      (fun y hy => (hA y hy).1)
  · exact closure_image_bound A x hx secondValue secondValue_within _ R.val
      (fun y hy => (hA y hy).2)

theorem square_of_ball_bound (x : PositionValue) (centre : Point)
    (R : NonnegativeRadius) (h : Within x.val (embed (centre,zeroPoint)) R.val) :
    CoordinateSquare centre R x :=
  ⟨firstValue_within _ _ _ h,secondValue_within _ _ _ h⟩

end NewtonLimitDynamics.Polygon.CompletionGeometry
