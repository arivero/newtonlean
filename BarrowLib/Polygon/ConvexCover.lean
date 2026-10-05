import BarrowLib.Polygon.PointBounds

/-!
Finite rational convex enclosures in the chosen coordinate L1 magnitude.
The square is an explicit point set; its area is a covering budget, not an
assertion about the area of a union of patches or a limiting trajectory.
-/

namespace NewtonLimitDynamics.Polygon.ConvexCover

open NewtonLimitDynamics
open TimeSubdivision
open PointBounds

def UnitInterval (a : Fraction) : Prop := 0 ≤ a.num ∧ a.num ≤ a.den

def complement (a : Fraction) : Fraction :=
  ⟨a.den - a.num, a.den, a.den_pos⟩

theorem complement_nonnegative (a : Fraction) (ha : UnitInterval a) :
    0 ≤ (complement a).num := by
  obtain ⟨_, hupper⟩ := ha
  unfold complement
  dsimp
  omega

theorem complement_abs (a : Fraction) (ha : UnitInterval a) :
    Fraction.equiv (complement a).abs (complement a) :=
  Fraction.abs_of_nonnegative _ (complement_nonnegative a ha)

theorem interval_abs (a : Fraction) (ha : UnitInterval a) :
    Fraction.equiv a.abs a := Fraction.abs_of_nonnegative _ ha.1

theorem weights_sum_one (a : Fraction) :
    Fraction.equiv (Fraction.add (complement a) a) (Fraction.ofInt 1) := by
  unfold complement Fraction.equiv Fraction.add Fraction.ofInt
  dsimp
  simp only [Int.sub_mul, Int.mul_sub]
  ac_nf
  omega

def lerp (a : Fraction) (p q : Point) : Point :=
  pointAdd (pointScale (complement a) p) (pointScale a q)

theorem pointSub_self_zero (p : Point) :
    Fraction.equiv (pointNorm (pointSub p p)) (Fraction.ofInt 0) := by
  have hz (a : Int) : (a + -a).natAbs = 0 := by omega
  simp only [pointNorm, pointSub, pointNeg, pointAdd, Fraction.equiv,
    Fraction.abs, Fraction.add, Fraction.ofInt,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  simp only [hz, Int.ofNat_zero, Int.zero_mul, Int.mul_zero, Int.add_zero]

theorem pointSub_chain (a b c : Point) :
    pointEquiv (pointSub a c)
      (pointAdd (pointSub a b) (pointSub b c)) := by
  constructor <;>
    simp only [pointSub, pointNeg, pointAdd, Fraction.equiv, Fraction.add,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

theorem pointSub_triangle (a b c : Point) :
    Fraction.le (pointNorm (pointSub a c))
      (Fraction.add (pointNorm (pointSub a b)) (pointNorm (pointSub b c))) :=
  Fraction.le_equiv_left (pointNorm_equiv (pointSub_chain a b c))
    (pointNorm_add_le (pointSub a b) (pointSub b c))

theorem drift_offset (h : Fraction) (x v : Point) :
    pointEquiv (pointSub (pointAdd x (pointScale h v)) x) (pointScale h v) := by
  constructor <;>
    simp only [pointSub, pointNeg, pointAdd, pointScale, Fraction.equiv,
      Fraction.add, Fraction.mul, Int.add_mul, Int.mul_add,
      Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- Translation of a lerp is the same weighted sum of endpoint offsets. -/
theorem lerp_offset (a : Fraction) (anchor p q : Point) :
    pointEquiv (pointSub (lerp a p q) anchor)
      (pointAdd (pointScale (complement a) (pointSub p anchor))
        (pointScale a (pointSub q anchor))) := by
  constructor <;>
    simp only [lerp, complement, pointEquiv, pointSub, pointNeg, pointAdd,
      pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub,
      Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- A convex combination of two points in the L1 ball remains in that ball. -/
theorem lerp_ball_bound (a : Fraction) (ha : UnitInterval a)
    (anchor p q : Point) (R : Fraction)
    (hp : Fraction.le (pointNorm (pointSub p anchor)) R)
    (hq : Fraction.le (pointNorm (pointSub q anchor)) R) :
    Fraction.le (pointNorm (pointSub (lerp a p q) anchor)) R := by
  let c := complement a
  let P := pointSub p anchor
  let Q := pointSub q anchor
  have ht := pointNorm_add_le (pointScale c P) (pointScale a Q)
  have hs : Fraction.equiv
      (Fraction.add (pointNorm (pointScale c P)) (pointNorm (pointScale a Q)))
      (Fraction.add (Fraction.mul c (pointNorm P)) (Fraction.mul a (pointNorm Q))) :=
    Fraction.add_equiv
      (Fraction.equiv_trans (pointNorm_scale c P)
        (Fraction.mul_equiv (complement_abs a ha) (Fraction.equiv_refl _)))
      (Fraction.equiv_trans (pointNorm_scale a Q)
        (Fraction.mul_equiv (interval_abs a ha) (Fraction.equiv_refl _)))
  have h₁ := Fraction.mul_le_mul_nonnegative_left hp c (complement_nonnegative a ha)
  have h₂ := Fraction.mul_le_mul_nonnegative_left hq a ha.1
  have hc := Fraction.add_le_add h₁ h₂
  have he : Fraction.equiv
      (Fraction.add (Fraction.mul c R) (Fraction.mul a R)) R := by
    have hw := weights_sum_one a
    have hm := Fraction.mul_equiv_left R hw
    have hz : Fraction.equiv (Fraction.mul (Fraction.add c a) R)
        (Fraction.add (Fraction.mul c R) (Fraction.mul a R)) := by
      simp only [Fraction.equiv, Fraction.add, Fraction.mul]
      simp only [Int.add_mul, Int.mul_add]
      ac_nf
    have hone : Fraction.equiv (Fraction.mul R (Fraction.ofInt 1)) R := by
      simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
      simp
    exact Fraction.equiv_trans (Fraction.equiv_symm hz)
      (Fraction.equiv_trans (Fraction.mul_comm (Fraction.add c a) R)
        (Fraction.equiv_trans hm hone))
  have hraw := Fraction.le_equiv_left (pointNorm_equiv (lerp_offset a anchor p q))
    (Fraction.le_equiv_right ht hs)
  exact Fraction.le_equiv_right (Fraction.magnitudes.le_trans hraw hc) he

def SquareContains (anchor : Point) (R : Fraction) (p : Point) : Prop :=
  Fraction.le (pointSub p anchor).1.abs R ∧
    Fraction.le (pointSub p anchor).2.abs R

theorem ball_inside_square (anchor p : Point) (R : Fraction)
    (h : Fraction.le (pointNorm (pointSub p anchor)) R) :
    SquareContains anchor R p := by
  constructor
  · exact Fraction.magnitudes.le_trans
      (Fraction.le_add_nonnegative _ _ (Fraction.abs_num_nonnegative _)) h
  · have h₂ := Fraction.le_add_nonnegative (pointSub p anchor).2.abs
      (pointSub p anchor).1.abs (Fraction.abs_num_nonnegative _)
    exact Fraction.magnitudes.le_trans
      (Fraction.le_equiv_right h₂
        (Fraction.add_comm (pointSub p anchor).2.abs (pointSub p anchor).1.abs)) h

/-- A matched quad patch uses one physical-time fraction `theta` on both
polygon edges, then interpolates between those simultaneous positions. -/
def matchedPatch (theta lambda : Fraction) (c0 c1 f0 f1 : Point) : Point :=
  lerp lambda (lerp theta c0 c1) (lerp theta f0 f1)

theorem matchedPatch_ball (theta lambda : Fraction)
    (ht : UnitInterval theta) (hl : UnitInterval lambda)
    (anchor c0 c1 f0 f1 : Point) (R : Fraction)
    (hc0 : Fraction.le (pointNorm (pointSub c0 anchor)) R)
    (hc1 : Fraction.le (pointNorm (pointSub c1 anchor)) R)
    (hf0 : Fraction.le (pointNorm (pointSub f0 anchor)) R)
    (hf1 : Fraction.le (pointNorm (pointSub f1 anchor)) R) :
    Fraction.le (pointNorm (pointSub
      (matchedPatch theta lambda c0 c1 f0 f1) anchor)) R :=
  lerp_ball_bound lambda hl anchor _ _ R
    (lerp_ball_bound theta ht anchor c0 c1 R hc0 hc1)
    (lerp_ball_bound theta ht anchor f0 f1 R hf0 hf1)

theorem matchedPatch_square (theta lambda : Fraction)
    (ht : UnitInterval theta) (hl : UnitInterval lambda)
    (anchor c0 c1 f0 f1 : Point) (R : Fraction)
    (hc0 : Fraction.le (pointNorm (pointSub c0 anchor)) R)
    (hc1 : Fraction.le (pointNorm (pointSub c1 anchor)) R)
    (hf0 : Fraction.le (pointNorm (pointSub f0 anchor)) R)
    (hf1 : Fraction.le (pointNorm (pointSub f1 anchor)) R) :
    SquareContains anchor R (matchedPatch theta lambda c0 c1 f0 f1) :=
  ball_inside_square anchor _ R
    (matchedPatch_ball theta lambda ht hl anchor c0 c1 f0 f1 R hc0 hc1 hf0 hf1)

theorem complement_interval (a : Fraction) (ha : UnitInterval a) :
    UnitInterval (complement a) := by
  obtain ⟨hl,hu⟩ := ha
  unfold UnitInterval complement
  dsimp
  omega

theorem lerp_zero (p q : Point) : pointEquiv (lerp (Fraction.ofInt 0) p q) p := by
  constructor <;>
    simp [lerp,complement,pointAdd,pointScale,Fraction.equiv,Fraction.add,
      Fraction.mul,Fraction.ofInt] <;> ac_nf

theorem lerp_one (p q : Point) : pointEquiv (lerp (Fraction.ofInt 1) p q) q := by
  constructor <;>
    simp [lerp,complement,pointAdd,pointScale,Fraction.equiv,Fraction.add,
      Fraction.mul,Fraction.ofInt] <;> ac_nf

theorem lerp_swap (a : Fraction) (p q : Point) :
    pointEquiv (lerp a p q) (lerp (complement a) q p) := by
  constructor <;>
    simp only [lerp,complement,pointAdd,pointScale,Fraction.equiv,Fraction.add,
      Fraction.mul,Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub] <;>
    ac_nf <;> omega

end NewtonLimitDynamics.Polygon.ConvexCover
