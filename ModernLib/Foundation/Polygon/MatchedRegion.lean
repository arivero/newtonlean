import ModernLib.Foundation.Polygon.SquareOuterContent
import ModernLib.Foundation.Polygon.BinaryEndpoints

/-! Unsigned matched regions for two maps on the constructed binary-time
domain. Each dyadic cell closes all simultaneous rational connectors; their
finite union counts overlaps once. Closed square enclosures and geometric
cover budgets are independent of the construction of either map. -/

namespace NewtonLimitDynamics.Polygon.MatchedRegion
open NewtonLimitDynamics
open TimeSubdivision HarmonicDyadic HarmonicBinaryPrefix BinaryTime CauchyValues PositionValues
open ConvexCover ConvexValues CompletionGeometry SquareOuterContent

def cellPatch (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m k : Nat) (x : PositionValue) : Prop :=
  ∃ b : Nat → Bool, ticks b m=k ∧ ∃ a : Fraction, ∃ ha : UnitInterval a,
    x=convexPosition a ha (p (Quotient.mk _ b)) (g (Quotient.mk _ b))

def Region (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m : Nat) (x : PositionValue) : Prop :=
  ∃ k, k<blocks m ∧ Closure (cellPatch T hT p g m k) x

-- Modern dependency score: 45/118 (M=45, H=73; transitive project theorems/axioms).
theorem cellPatch_square (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m : Nat)
    (centres : Nat → Point) (R : NonnegativeRadius)
    (h : ∀ b : Nat → Bool,
      CoordinateSquare (centres (ticks b m)) R (p (Quotient.mk _ b)) ∧
      CoordinateSquare (centres (ticks b m)) R (g (Quotient.mk _ b)))
    (k : Nat) (x : PositionValue) (hx : cellPatch T hT p g m k x) :
    CoordinateSquare (centres k) R x := by
  obtain ⟨b,hb,a,ha,hx⟩ := hx
  subst x
  obtain ⟨hp,hg⟩ := h b
  rw [hb] at hp hg
  exact convexPosition_square a ha _ _ _ _ hp hg

-- Modern dependency score: 58/131 (M=58, H=73; transitive project theorems/axioms).
theorem closed_cell_square (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m : Nat)
    (centres : Nat → Point) (R : NonnegativeRadius)
    (h : ∀ b : Nat → Bool,
      CoordinateSquare (centres (ticks b m)) R (p (Quotient.mk _ b)) ∧
      CoordinateSquare (centres (ticks b m)) R (g (Quotient.mk _ b)))
    (k : Nat) (x : PositionValue) (hx : Closure (cellPatch T hT p g m k) x) :
    CoordinateSquare (centres k) R x :=
  closure_square _ x hx _ _ (fun y hy => cellPatch_square T hT p g m centres R h k y hy)

def actualCover (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m : Nat)
    (centres : Nat → Point) (R : NonnegativeRadius)
    (h : ∀ b : Nat → Bool,
      CoordinateSquare (centres (ticks b m)) R (p (Quotient.mk _ b)) ∧
      CoordinateSquare (centres (ticks b m)) R (g (Quotient.mk _ b))) :
    Cover (Region T hT p g m) where
  count := blocks m
  squares := fun k => ⟨centres k,R⟩
  covers := by
    intro x hx
    obtain ⟨k,hk,hx⟩ := hx
    exact ⟨k,hk,closed_cell_square T hT p g m centres R h k x hx⟩

-- Modern dependency score: 37/101 (M=37, H=64; transitive project theorems/axioms).
theorem connector_in_region (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m : Nat)
    (t : BinaryTime T hT) (a : Fraction) (ha : UnitInterval a) :
    Region T hT p g m (convexPosition a ha (p t) (g t)) := by
  induction t using Quotient.inductionOn with
  | _ b =>
    exact ⟨ticks b m,ticks_lt_blocks b m,closure_contains _ _ ⟨b,rfl,a,ha,rfl⟩⟩

-- Modern dependency score: 41/113 (M=41, H=72; transitive project theorems/axioms).
theorem reversed_connector_in_region (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m : Nat)
    (t : BinaryTime T hT) (a : Fraction) (ha : UnitInterval a) :
    Region T hT p g m (convexPosition a ha (g t) (p t)) := by
  rw [convexPosition_swap]
  exact connector_in_region T hT p g m t _ (complement_interval a ha)

-- Modern dependency score: 41/112 (M=41, H=71; transitive project theorems/axioms).
theorem polygon_in_region (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m : Nat) (t : BinaryTime T hT) :
    Region T hT p g m (p t) := by
  have ha : UnitInterval (Fraction.ofInt 0) := by constructor <;> decide
  have h := connector_in_region T hT p g m t (Fraction.ofInt 0) ha
  rwa [convexPosition_zero] at h

-- Modern dependency score: 41/112 (M=41, H=71; transitive project theorems/axioms).
theorem curve_in_region (T : Fraction) (hT : 0 ≤ T.num)
    (p g : BinaryTime T hT → PositionValue) (m : Nat) (t : BinaryTime T hT) :
    Region T hT p g m (g t) := by
  have ha : UnitInterval (Fraction.ofInt 1) := by constructor <;> decide
  have h := connector_in_region T hT p g m t (Fraction.ofInt 1) ha
  rwa [convexPosition_one] at h

/-- With one square of radius C/2^m per cell, the total budget is 4*C²/2^m.
This is cover arithmetic; membership and the actual enclosure are proved above. -/
-- Modern dependency score: 1/12 (M=1, H=11; transitive project theorems/axioms).
theorem uniform_budget_geometric (centres : Nat → Point) (R : NonnegativeRadius)
    (m : Nat) (C : Fraction) (hr : Fraction.equiv R.val (duration C m)) :
    Fraction.equiv (sumBudget (fun k => ⟨centres k,R⟩) (blocks m))
      (duration (squareArea C) m) := by
  have hc := Fraction.mul_equiv (Fraction.equiv_refl (Fraction.ofInt (blocks m : Int)))
    (Fraction.mul_equiv (Fraction.equiv_refl (Fraction.ofInt 4)) (Fraction.mul_equiv hr hr))
  apply Fraction.equiv_trans (uniform_budget centres R (blocks m))
  apply Fraction.equiv_trans hc
  simp only [squareArea,duration,blocks,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_pow]
  ac_nf

end NewtonLimitDynamics.Polygon.MatchedRegion
