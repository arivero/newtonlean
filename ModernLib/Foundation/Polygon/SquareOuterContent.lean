import ModernLib.Foundation.Polygon.CompletionGeometry
import BarrowLib.Common.RationalExhaustion

/-! Nonnegative elementary outer content in the completed coordinate plane.
A cover is a finite family of closed rational squares. Its budget counts
squares with multiplicity; the region is a point set, so overlapping or crossing
lobes have no signed cancellation. Content is the closed lower cut of the
infimum of all covering budgets, rather than an arbitrary chosen cover budget. -/
namespace NewtonLimitDynamics.Polygon.SquareOuterContent
open NewtonLimitDynamics
open TimeSubdivision CauchyValues PositionValues

structure Square where
  centre : Point
  radius : NonnegativeRadius

def Square.Contains (q : Square) (x : PositionValue) : Prop :=
  CoordinateSquare q.centre q.radius x

def squareArea (R : Fraction) : Fraction :=
  Fraction.mul (Fraction.ofInt 4) (Fraction.mul R R)

def Square.area (q : Square) : Fraction := squareArea q.radius.val

-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
theorem squareArea_nonnegative (R : Fraction) (hR : 0 ≤ R.num) :
    0 ≤ (squareArea R).num :=
  Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hR hR)

def sumBudget (squares : Nat → Square) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | n+1 => Fraction.add (sumBudget squares n) (squares n).area

-- Modern dependency score: 1/3 (M=1, H=2; transitive project theorems/axioms).
theorem sumBudget_nonnegative (squares : Nat → Square) :
    ∀ n, 0 ≤ (sumBudget squares n).num
  | 0 => by simp [sumBudget,Fraction.ofInt]
  | n+1 => Fraction.nonnegative_add _ _ (sumBudget_nonnegative squares n)
      (squareArea_nonnegative _ (squares n).radius.property)

structure Cover (A : PositionValue → Prop) where
  count : Nat
  squares : Nat → Square
  covers : ∀ x, A x → ∃ k, k < count ∧ (squares k).Contains x

def Cover.budget {A : PositionValue → Prop} (c : Cover A) : Fraction :=
  sumBudget c.squares c.count

-- Modern dependency score: 13/51 (M=13, H=38; transitive project theorems/axioms).
theorem Cover.budget_nonnegative {A : PositionValue → Prop} (c : Cover A) :
    0 ≤ c.budget.num := sumBudget_nonnegative c.squares c.count

def Cover.restrict {A B : PositionValue → Prop} (c : Cover B)
    (h : ∀ x, A x → B x) : Cover A :=
  ⟨c.count,c.squares,fun x hx => c.covers x (h x hx)⟩

-- Modern dependency score: 0/8 (M=0, H=8; transitive project theorems/axioms).
theorem uniform_budget (centres : Nat → Point) (R : NonnegativeRadius) :
    ∀ n, Fraction.equiv (sumBudget (fun k => ⟨centres k,R⟩) n)
      (Fraction.mul (Fraction.ofInt (n : Int)) (squareArea R.val))
  | 0 => by simp [sumBudget,Fraction.equiv,Fraction.mul,Fraction.ofInt]
  | n+1 => by
      have he := Fraction.add_equiv (uniform_budget centres R n)
        (Fraction.equiv_refl (squareArea R.val))
      apply Fraction.equiv_trans he
      simp only [Square.area,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
      ac_nf

/-- Exact lower-cut representation of the infimum over all finite square covers.
If no cover exists this is an unbounded cut; bounded regions below supply a
constructed cover and therefore a finite upper bound. -/
def LowerContent (A : PositionValue → Prop) (q : Fraction) : Prop :=
  ∀ c : Cover A, Fraction.le q c.budget

-- Modern dependency score: 14/52 (M=14, H=38; transitive project theorems/axioms).
theorem content_zero_lower (A : PositionValue → Prop) :
    LowerContent A (Fraction.ofInt 0) := by
  intro c
  simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using c.budget_nonnegative

-- Modern dependency score: 11/47 (M=11, H=36; transitive project theorems/axioms).
theorem content_downward (A : PositionValue → Prop) (p q : Fraction)
    (hpq : Fraction.le p q) (hq : LowerContent A q) : LowerContent A p := by
  intro c
  exact Fraction.magnitudes.le_trans hpq (hq c)

/-- The infimum cut is closed under exhaustion from its lower bounds. -/
-- Modern dependency score: 11/48 (M=11, H=37; transitive project theorems/axioms).
theorem content_closed (A : PositionValue → Prop) (q : Fraction)
    (h : ∀ eps : Fraction, 0 < eps.num →
      ∃ p, LowerContent A p ∧ Fraction.le q (Fraction.add p eps)) :
    LowerContent A q := by
  intro c
  apply Fraction.le_of_enlargements
  intro eps heps
  obtain ⟨p,hp,hqp⟩ := h eps heps
  exact Fraction.magnitudes.le_trans hqp (Fraction.add_le_add_right (hp c) eps)

-- Modern dependency score: 11/47 (M=11, H=36; transitive project theorems/axioms).
theorem content_cover_bound (A : PositionValue → Prop) (c : Cover A)
    (q : Fraction) (hq : LowerContent A q) : Fraction.le q c.budget := hq c

-- Modern dependency score: 23/62 (M=23, H=39; transitive project theorems/axioms).
theorem content_mono (A B : PositionValue → Prop)
    (hAB : ∀ x, A x → B x) (q : Fraction) (hq : LowerContent A q) :
    LowerContent B q := by
  intro c
  exact hq (c.restrict hAB)

-- Modern dependency score: 24/63 (M=24, H=39; transitive project theorems/axioms).
theorem content_union_includes (A B : PositionValue → Prop) (q : Fraction)
    (h : LowerContent A q ∨ LowerContent B q) :
    LowerContent (fun x => A x ∨ B x) q := by
  cases h with
  | inl h => exact content_mono A _ (fun _ hx => Or.inl hx) q h
  | inr h => exact content_mono B _ (fun _ hx => Or.inr hx) q h

/-- Empty regions have content zero; this also checks the zero-square budget. -/
def emptyCover : Cover (fun _ => False) where
  count := 0
  squares := fun _ => ⟨zeroPoint,⟨Fraction.ofInt 0,by decide⟩⟩
  covers := fun _ h => False.elim h

-- Modern dependency score: 28/69 (M=28, H=41; transitive project theorems/axioms).
theorem empty_content (q : Fraction) :
    LowerContent (fun _ => False) q ↔ Fraction.le q (Fraction.ofInt 0) := by
  constructor
  · intro h
    exact h emptyCover
  · intro h
    exact content_downward _ q _ h (content_zero_lower _)

/-- Both singleton and zero-radius controls use actual completed-square membership. -/
def singletonCover (p : Point) : Cover (fun x => x = embedPosition p) where
  count := 1
  squares := fun _ => ⟨p,⟨Fraction.ofInt 0,by decide⟩⟩
  covers := by
    intro x hx
    subst x
    refine ⟨0,by decide,?_⟩
    constructor <;> exact (within_zero_iff _ _).mpr rfl

-- Modern dependency score: 31/72 (M=31, H=41; transitive project theorems/axioms).
theorem singleton_content (p : Point) (q : Fraction) :
    LowerContent (fun x => x = embedPosition p) q ↔ Fraction.le q (Fraction.ofInt 0) := by
  constructor
  · intro h
    have hb := h (singletonCover p)
    exact Fraction.le_equiv_right hb (by
      simp [Cover.budget,singletonCover,sumBudget,Square.area,squareArea,
        Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt])
  · intro h
    exact content_downward _ q _ h (content_zero_lower _)

end NewtonLimitDynamics.Polygon.SquareOuterContent
