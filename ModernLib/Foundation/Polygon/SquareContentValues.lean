import ModernLib.Foundation.Polygon.SquareOuterContent
import ModernLib.Foundation.Polygon.BoundedCuts

/-! The elementary all-cover outer-content cut is realized as a Cauchy scalar
by shrinking rational intervals. Different proved initial covers produce the
same value. An ordinary measure or inner-area identification remains separate. -/
namespace NewtonLimitDynamics.Polygon.SquareContentValues
open NewtonLimitDynamics
open TimeSubdivision HarmonicDyadic CauchyValues PositionValues BinaryTime ScalarOrder
open SquareOuterContent

def contentCut (A : PositionValue → Prop) (c : Cover A) : BoundedCuts.Cut where
  lower := LowerContent A
  zero_lower := content_zero_lower A
  downward := content_downward A
  closed := content_closed A
  bound := c.budget
  bound_nonnegative := c.budget_nonnegative
  bounded := fun _ hq => hq c

noncomputable def contentName (A : PositionValue → Prop) (c : Cover A) : EndpointCauchyName :=
  BoundedCuts.name (contentCut A c)

noncomputable def contentValue (A : PositionValue → Prop) (c : Cover A) : ScalarValue :=
  BoundedCuts.value (contentCut A c)

theorem contentValue_lower_cut (A : PositionValue → Prop) (c : Cover A) (q : Fraction) :
    Below q (contentValue A c).val ↔ LowerContent A q :=
  BoundedCuts.value_realizes_cut (contentCut A c) q

theorem contentValue_nonnegative (A : PositionValue → Prop) (c : Cover A) :
    Below (Fraction.ofInt 0) (contentValue A c).val :=
  BoundedCuts.value_nonnegative (contentCut A c)

theorem contentValue_within_zero (A : PositionValue → Prop) (c : Cover A) :
    Within (contentValue A c).val (embed (scalarState (Fraction.ofInt 0))) c.budget :=
  BoundedCuts.value_within_zero (contentCut A c)

theorem contentValue_independent_cover (A : PositionValue → Prop) (c d : Cover A) :
    contentValue A c = contentValue A d :=
  BoundedCuts.value_eq_of_lower_iff (contentCut A c) (contentCut A d) (fun _ => Iff.rfl)

/-- Equal point sets have the same scalar content, even when their proved
initial covers and bounds differ. -/
theorem contentValue_region_congr (A B : PositionValue → Prop)
    (h : ∀ x, A x ↔ B x) (c : Cover A) (d : Cover B) :
    contentValue A c = contentValue B d :=
  BoundedCuts.value_eq_of_lower_iff (contentCut A c) (contentCut B d) (fun q =>
    ⟨content_mono A B (fun x hx => (h x).mp hx) q,
     content_mono B A (fun x hx => (h x).mpr hx) q⟩)

/-- Any actual cover bounds the canonical value, regardless of the cover used
for its bisection construction. -/
theorem contentValue_any_cover_bound (A : PositionValue → Prop) (c d : Cover A) :
    Within (contentValue A c).val (embed (scalarState (Fraction.ofInt 0))) d.budget := by
  rw [contentValue_independent_cover A c d]
  exact contentValue_within_zero A d

theorem empty_value_zero :
    (contentValue (fun _ => False) emptyCover).val = embed (scalarState (Fraction.ofInt 0)) :=
  BoundedCuts.value_zero_of_bound_zero _ rfl

theorem singleton_value_zero (p : Point) :
    (contentValue (fun x => x = embedPosition p) (singletonCover p)).val =
      embed (scalarState (Fraction.ofInt 0)) :=
  BoundedCuts.value_zero_of_bound_zero _ rfl

end NewtonLimitDynamics.Polygon.SquareContentValues
