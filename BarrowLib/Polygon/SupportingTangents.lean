import BarrowLib.Polygon.ConvexCover
import BarrowLib.Polygon.DyadicArithmetic
import BarrowLib.Polygon.FiniteEstimates
import BarrowLib.Polygon.Parallelogram

/-! Finite supporting-line geometry for a monotone curve cell. The endpoint
support inequalities concern the two lines, not their desired intersection
or enclosure. A crossing is constructed even when the lines coincide. The
joined finite segments, rather than the whole infinite supporting lines, are
the boundary used by a circumscribed polygon. No differentiability or curve
limit is assumed or proved here. -/

namespace NewtonLimitDynamics.Polygon.SupportingTangents
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates ConvexCover
open HarmonicTimeComparison HarmonicStability

def affine (a u v : Fraction) : Fraction :=
  Fraction.add (Fraction.mul (complement a) u) (Fraction.mul a v)

theorem affine_between (a u v : Fraction) (ha : UnitInterval a)
    (h : Fraction.le u v) :
    Fraction.le u (affine a u v) ∧ Fraction.le (affine a u v) v := by
  have hconst (x : Fraction) : Fraction.equiv (affine a x x) x := by
    exact Fraction.equiv_trans
      (Fraction.equiv_symm (Fraction.add_mul (complement a) a x))
      (Fraction.equiv_trans (Fraction.mul_equiv_right x (weights_sum_one a))
        (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]))
  constructor
  · exact Fraction.le_equiv_left (Fraction.equiv_symm (hconst u))
      (Fraction.add_le_add (Fraction.magnitudes.le_refl _)
        (Fraction.mul_le_mul_nonnegative_left h a ha.1))
  · exact Fraction.le_equiv_right
      (Fraction.add_le_add
        (Fraction.mul_le_mul_nonnegative_left h (complement a) (complement_nonnegative a ha))
        (Fraction.magnitudes.le_refl _)) (hconst v)

private theorem balance (s d : Fraction) (hs : 0≤s.num) (hd : 0≤d.num) :
    ∃ a : Fraction, UnitInterval a ∧
      Fraction.equiv (Fraction.mul (complement a) s) (Fraction.mul a d) := by
  let S := s.num*d.den
  let D := d.num*s.den
  have hS : 0≤S := Int.mul_nonneg hs (Int.le_of_lt d.den_pos)
  have hD : 0≤D := Int.mul_nonneg hd (Int.le_of_lt s.den_pos)
  by_cases hp : 0<S+D
  · let a : Fraction := ⟨S,S+D,hp⟩
    refine ⟨a,⟨hS,by dsimp [a]; omega⟩,?_⟩
    simp only [a,complement,Fraction.equiv,Fraction.mul]
    dsimp [S,D]
    simp only [Int.sub_mul,Int.add_mul,Int.mul_sub,Int.mul_add]
    ac_nf
    omega
  · have hz : S=0 := by omega
    have hs0 : s.num=0 := (Int.mul_eq_zero.mp hz).resolve_right (Int.ne_of_gt d.den_pos)
    refine ⟨Fraction.ofInt 0,by constructor <;> decide,?_⟩
    simp only [complement,Fraction.equiv,Fraction.mul,Fraction.ofInt,hs0,
      Int.zero_mul,Int.mul_zero]

/-- Two affine heights with opposite endpoint order meet at a rational cell
parameter. The zero-slack case chooses the left endpoint and requires no
unique intersection of coincident lines. -/
theorem affine_crossing (l0 l1 r0 r1 : Fraction)
    (hs : (Fraction.le l0 r0 ∧ Fraction.le r1 l1) ∨
      (Fraction.le r0 l0 ∧ Fraction.le l1 r1)) :
    ∃ a : Fraction, UnitInterval a ∧
      Fraction.equiv (affine a l0 l1) (affine a r0 r1) := by
  have ordered (u0 u1 v0 v1 : Fraction)
      (h0 : Fraction.le u0 v0) (h1 : Fraction.le v1 u1) :
      ∃ a : Fraction, UnitInterval a ∧
        Fraction.equiv (affine a u0 u1) (affine a v0 v1) := by
    obtain ⟨a,ha,hb⟩ := balance (durationDifference u0 v0) (durationDifference v1 u1)
      ((difference_nonnegative_iff _ _).mpr h0) ((difference_nonnegative_iff _ _).mpr h1)
    refine ⟨a,ha,?_⟩
    have he : Fraction.equiv
        (Fraction.add (Fraction.mul (complement a) (durationDifference u0 v0))
          (affine a u0 u1))
        (Fraction.add (Fraction.mul a (durationDifference v1 u1))
          (affine a v0 v1)) := by
      simp only [durationDifference,negF,affine,Fraction.equiv,Fraction.add,Fraction.mul,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
      ac_nf
      omega
    have he' := Fraction.equiv_trans
      (Fraction.add_equiv (Fraction.equiv_symm hb) (Fraction.equiv_refl _)) he
    exact (Fraction.equiv_iff_mutual_le _ _).mpr
      ⟨Fraction.le_add_cancel_left _ _ _ (Fraction.le_of_equiv he'),
        Fraction.le_add_cancel_left _ _ _ (Fraction.le_of_equiv (Fraction.equiv_symm he'))⟩
  rcases hs with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact ordered l0 l1 r0 r1 h0 h1
  · obtain ⟨a,ha,he⟩ := ordered r0 r1 l0 l1 h0 h1
    exact ⟨a,ha,Fraction.equiv_symm he⟩

def Between (a x b : Fraction) : Prop :=
  (Fraction.le a x ∧ Fraction.le x b) ∨ (Fraction.le b x ∧ Fraction.le x a)

def RectangleBetween (p x q : Point) : Prop :=
  Between p.1 x.1 q.1 ∧ Between p.2 x.2 q.2

/-- The two endpoint lines are represented over the same horizontal cell:
`p → leftEnd` and `rightStart → q`. Both are monotone in the same vertical
direction. Either the upper-support or lower-support orientation is allowed.
Vertical supporting lines are not graphs over a nonzero horizontal cell;
they require a different coordinate patch. -/
structure Cell (p q : Point) where
  leftEnd : Point
  rightStart : Point
  left_x : Fraction.equiv leftEnd.1 q.1
  right_x : Fraction.equiv rightStart.1 p.1
  support : (Fraction.le p.2 rightStart.2 ∧ Fraction.le q.2 leftEnd.2) ∨
    (Fraction.le rightStart.2 p.2 ∧ Fraction.le leftEnd.2 q.2)
  monotone : (Fraction.le p.2 leftEnd.2 ∧ Fraction.le rightStart.2 q.2) ∨
    (Fraction.le leftEnd.2 p.2 ∧ Fraction.le q.2 rightStart.2)

def Meeting (p q : Point) (c : Cell p q) (x : Point) : Prop :=
  ∃ a : Fraction, UnitInterval a ∧ pointEquiv x (lerp a p c.leftEnd) ∧
    pointEquiv x (lerp a c.rightStart q)

/-- Construct the finite meeting from the supporting inequalities. This does
not assume it lies in the rectangle, and does not exclude coincident lines. -/
theorem meeting_exists (p q : Point) (c : Cell p q) : ∃ x : Point, Meeting p q c x := by
  obtain ⟨a,ha,he⟩ := affine_crossing p.2 c.leftEnd.2 c.rightStart.2 q.2 c.support
  refine ⟨lerp a p c.leftEnd,a,ha,⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,?_,he⟩
  exact Fraction.add_equiv
    (Fraction.mul_equiv_left (complement a) (Fraction.equiv_symm c.right_x))
    (Fraction.mul_equiv_left a c.left_x)

theorem meeting_on_lines (p q : Point) (c : Cell p q) (x : Point)
    (hx : Meeting p q c x) :
    Parallelogram.ParallelThrough x p (pointSub c.leftEnd p) ∧
      Parallelogram.ParallelThrough x c.rightStart (pointSub q c.rightStart) := by
  obtain ⟨a,_,hl,hr⟩ := hx
  exact ⟨Fraction.equiv_trans
      (det_congr hl ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (Parallelogram.segment_on_line a p c.leftEnd),
    Fraction.equiv_trans (det_congr hr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (Parallelogram.segment_on_line a c.rightStart q)⟩

/-- Any intersection of two independent supporting lines equals the meeting
constructed above. Coincident lines use finite joined segments instead. -/
theorem meeting_unique (p q : Point) (c : Cell p q) (r x : Point)
    (hr : Meeting p q c r)
    (h : (det (pointSub c.leftEnd p) (pointSub q c.rightStart)).num≠0)
    (hx : Parallelogram.ParallelThrough x p (pointSub c.leftEnd p))
    (hy : Parallelogram.ParallelThrough x c.rightStart (pointSub q c.rightStart)) :
    pointEquiv x r := by
  have hs := meeting_on_lines p q c r hr
  exact det_coordinates_injective _ _ h
    (Fraction.equiv_trans hy (Fraction.equiv_symm hs.2))
    (Fraction.equiv_trans hx (Fraction.equiv_symm hs.1))

/-- The meeting lies between both endpoint coordinates. Decreasing patches,
both support orientations, horizontal cells and coincident lines are included.
No rectangle enclosure appears in the premises. -/
theorem meeting_rectangle (p q : Point) (c : Cell p q) (x : Point)
    (hx : Meeting p q c x) : RectangleBetween p x q := by
  obtain ⟨a,ha,hl,hr⟩ := hx
  constructor
  · have he : Fraction.equiv x.1 (affine a p.1 q.1) :=
      Fraction.equiv_trans hl.1 (Fraction.add_equiv (Fraction.equiv_refl _)
        (Fraction.mul_equiv_left a c.left_x))
    by_cases h : Fraction.le p.1 q.1
    · obtain ⟨h0,h1⟩ := affine_between a p.1 q.1 ha h
      exact Or.inl ⟨Fraction.le_equiv_right h0 (Fraction.equiv_symm he),Fraction.le_equiv_left he h1⟩
    · have h' : Fraction.le q.1 p.1 := by unfold Fraction.le at *; omega
      have hb := affine_between (complement a) q.1 p.1
        ⟨complement_nonnegative a ha,by dsimp [complement]; have := ha.1; omega⟩ h'
      have hs : Fraction.equiv (affine a p.1 q.1) (affine (complement a) q.1 p.1) := by
        simp only [affine,complement,Fraction.equiv,Fraction.add,Fraction.mul,
          Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub]
        ac_nf
        omega
      have he' := Fraction.equiv_trans he hs
      exact Or.inr ⟨Fraction.le_equiv_right hb.1 (Fraction.equiv_symm he'),Fraction.le_equiv_left he' hb.2⟩
  · rcases c.monotone with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact Or.inl ⟨Fraction.le_equiv_right (affine_between a _ _ ha h0).1
        (Fraction.equiv_symm hl.2),Fraction.le_equiv_left hr.2 (affine_between a _ _ ha h1).2⟩
    · have rev (u v : Fraction) (h : Fraction.le v u) :
          Fraction.le v (affine a u v) ∧ Fraction.le (affine a u v) u := by
        have hc (z : Fraction) : Fraction.equiv (affine a z z) z := by
          simp only [affine,complement,Fraction.equiv,Fraction.add,Fraction.mul,
            Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub]
          ac_nf
          omega
        exact ⟨Fraction.le_equiv_left (Fraction.equiv_symm (hc v))
          (Fraction.add_le_add
            (Fraction.mul_le_mul_nonnegative_left h (complement a) (complement_nonnegative a ha))
            (Fraction.magnitudes.le_refl _)),
          Fraction.le_equiv_right (Fraction.add_le_add (Fraction.magnitudes.le_refl _)
            (Fraction.mul_le_mul_nonnegative_left h a ha.1)) (hc u)⟩
      exact Or.inr ⟨Fraction.le_equiv_right (rev _ _ h1).1
        (Fraction.equiv_symm hr.2),Fraction.le_equiv_left hl.2 (rev _ _ h0).2⟩

/-- Every point of the endpoint rectangle is no farther from an endpoint
than the opposite endpoint, in the coordinate L1 magnitude. -/
theorem rectangle_distance_bound (p x q : Point) (hx : RectangleBetween p x q) :
    Fraction.le (pointDistance x p) (pointDistance q p) := by
  have bound (a b z : Fraction) (hz : Between a z b) :
      Fraction.le (durationDifference a z).abs (durationDifference a b).abs := by
    rcases hz with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact (difference_interval_gaps _ _ _ h0 h1).1
    · exact Fraction.le_equiv_right
        (Fraction.le_equiv_left (HarmonicTimeRealization.durationDifference_abs_symm a z)
          (difference_interval_gaps b z a h0 h1).2) (HarmonicTimeRealization.durationDifference_abs_symm b a)
  exact Fraction.add_le_add (bound p.1 q.1 x.1 hx.1) (bound p.2 q.2 x.2 hx.2)

end NewtonLimitDynamics.Polygon.SupportingTangents
