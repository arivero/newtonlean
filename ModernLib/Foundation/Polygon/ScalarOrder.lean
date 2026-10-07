import ModernLib.Foundation.Polygon.PositionValues
import ModernLib.Foundation.Polygon.BinaryTime
import BarrowLib.Common.RationalExhaustion

/-! A closed rational lower comparison for the first scalar coordinate of a
constructed Cauchy value. Representative invariance is proved before lifting. -/
namespace NewtonLimitDynamics.Polygon.ScalarOrder
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicTimeComparison
open HarmonicComparison CauchyValues PositionValues BinaryTime

-- Modern dependency score: 4/14 (M=4, H=10; transitive project theorems/axioms).
theorem first_coordinate_gap (a b : Point × Point) :
    Fraction.le (durationDifference b.1.1 a.1.1).abs (distance a b) :=
  Fraction.le_equiv_left (Fraction.equiv_symm (scalarState_distance a.1.1 b.1.1))
    (first_nonexpansive a b)

def NameBelow (q : Fraction) (a : EndpointCauchyName) : Prop :=
  ∀ eps : Fraction, 0 < eps.num → ∃ N, ∀ n, N ≤ n →
    Fraction.le q (Fraction.add (a.approx n).1.1 eps)

-- Modern dependency score: 5/28 (M=5, H=23; transitive project theorems/axioms).
theorem nameBelow_transport (q : Fraction) (a b : EndpointCauchyName)
    (hab : NameEquiv a b) (ha : NameBelow q a) : NameBelow q b := by
  intro eps heps
  obtain ⟨N,hN⟩ := ha eps.half heps
  obtain ⟨M,hM⟩ := hab eps.half heps
  refine ⟨max N M,?_⟩
  intro n hn
  have hg := Fraction.magnitudes.le_trans (first_coordinate_gap (a.approx n) (b.approx n))
    (Fraction.magnitudes.lt_implies_le (hM n (Nat.le_trans (Nat.le_max_right _ _) hn)))
  have hc := difference_add_bound (b.approx n).1.1 (a.approx n).1.1 eps.half
    (Fraction.magnitudes.le_trans (Fraction.le_abs _) hg)
  have hq := Fraction.magnitudes.le_trans
    (hN n (Nat.le_trans (Nat.le_max_left _ _) hn)) (Fraction.add_le_add_right hc eps.half)
  exact Fraction.le_equiv_right hq (Fraction.equiv_trans
    (Fraction.add_assoc _ eps.half eps.half)
    (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.half_add_self eps)))

-- Modern dependency score: 7/37 (M=7, H=30; transitive project theorems/axioms).
theorem nameBelow_congr (q : Fraction) (a b : EndpointCauchyName)
    (hab : NameEquiv a b) : NameBelow q a ↔ NameBelow q b :=
  ⟨nameBelow_transport q a b hab,nameBelow_transport q b a (nameEquiv_symm hab)⟩

def Below (q : Fraction) (v : Value) : Prop :=
  Quotient.liftOn v (fun a => NameBelow q a)
    (fun a b h => propext (nameBelow_congr q a b h))

-- Modern dependency score: 14/56 (M=14, H=42; transitive project theorems/axioms).
theorem below_realize (q : Fraction) (a : EndpointCauchyName) :
    Below q (realize a) ↔ NameBelow q a := Iff.rfl

-- Modern dependency score: 14/57 (M=14, H=43; transitive project theorems/axioms).
theorem below_embed_iff (q : Fraction) (s : Point × Point) :
    Below q (embed s) ↔ Fraction.le q s.1.1 := by
  constructor
  · intro h
    apply Fraction.le_of_enlargements
    intro eps heps
    obtain ⟨N,hN⟩ := h eps heps
    exact hN N (Nat.le_refl _)
  · intro h eps heps
    exact ⟨0,fun _ _ => Fraction.magnitudes.le_trans h
      (Fraction.le_add_nonnegative _ _ (Int.le_of_lt heps))⟩

-- Modern dependency score: 14/56 (M=14, H=42; transitive project theorems/axioms).
theorem below_downward (p q : Fraction) (v : Value)
    (hpq : Fraction.le p q) (hq : Below q v) : Below p v := by
  induction v using Quotient.inductionOn with
  | _ a =>
    intro eps heps
    obtain ⟨N,hN⟩ := hq eps heps
    exact ⟨N,fun n hn => Fraction.magnitudes.le_trans hpq (hN n hn)⟩

/-- Values fixed by the first-coordinate projection have no other component. -/
def ScalarValue := {v : Value // firstValue v = v}

end NewtonLimitDynamics.Polygon.ScalarOrder
