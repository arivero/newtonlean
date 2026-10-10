import BarrowLib.Polygon.RadialSector
import BarrowLib.Common.SimplexExit

/-! Rational finite triangle exchange, supporting the fan-collar inclusion.
Source of the coordinate statements below: the original English statements
and Lean derivations in this file. This is project proof provenance, without
external textual attribution, historical dating or a priority claim. The
mathematical dependencies are elementary Barrow/Classics support only.

Proved scope: for the fixed origin O and positive horizontal A,Q with
nonnegative determinant, a point of O,A,Q belongs to O,A,P or A,P,Q or O,P,Q,
with arbitrary rational P. The positive-determinant proof also works without
the half-plane premise. The zero case uses an ordered radial segment.
Do not assume the exchange inclusion or the
mechanical/sample-chord sector-difference inclusion. This file alone does
not assign an area to any triangle or finite union. -/
namespace NewtonLimitDynamics.Polygon.TriangleExchange
open NewtonLimitDynamics TimeSubdivision ConvexCover SectorFan
open HarmonicStability HarmonicDyadic HarmonicTimeComparison

/-- Translation of the origin-based filled triangle. -/
def TriangleAt (a b c x : Point) : Prop :=
  Triangle (pointSub b a) (pointSub c a) (pointSub x a)

/-- Dividing by a positive rational value cancels that value even when the
numerator is negative. Source: this original arithmetic derivation. -/
theorem quotient_mul (a b : Fraction) (hb : 0 < b.num) :
    Fraction.equiv (Fraction.mul (Fraction.quotient a b hb) b) a := by
  simp only [Fraction.equiv,Fraction.quotient,Fraction.mul]
  ac_nf

theorem det_swap_neg (a b : Point) : Fraction.equiv (det a b) (negF (det b a)) := by
  simp only [det,negF,Fraction.equiv,Fraction.add,Fraction.mul,Int.neg_mul,Int.mul_neg,
    Int.neg_add,Int.add_mul,Int.mul_add,Int.neg_neg]
  ac_nf

/-- Every point has explicit rational coordinates in an oriented independent
pair. No nonnegative-coordinate premise is imposed on the inserted point. -/
theorem coordinates (a b p : Point) (hd : 0 < (det a b).num) :
    pointEquiv p (pointAdd
      (pointScale (Fraction.quotient (det p b) (det a b) hd) a)
      (pointScale (Fraction.quotient (negF (det p a)) (det a b) hd) b)) := by
  let u := Fraction.quotient (det p b) (det a b) hd
  let v := Fraction.quotient (negF (det p a)) (det a b) hd
  apply det_coordinates_injective a b (Int.ne_of_gt hd)
  · apply Fraction.equiv_symm
    exact Fraction.equiv_trans (det_add_left b _ _)
      (Fraction.equiv_trans (Fraction.add_equiv
        (Fraction.equiv_trans (det_scale_left u b a) (quotient_mul (det p b) (det a b) hd))
        (Fraction.equiv_trans (det_scale_left v b b)
          (Fraction.equiv_trans (Fraction.mul_equiv_left v (det_self b)) (Fraction.mul_zero v))))
        (Fraction.add_zero _))
  · apply Fraction.equiv_symm
    apply Fraction.equiv_trans (det_add_left a _ _)
    apply Fraction.equiv_trans (Fraction.add_equiv
      (Fraction.equiv_trans (det_scale_left u a a)
        (Fraction.equiv_trans (Fraction.mul_equiv_left u (det_self a)) (Fraction.mul_zero u)))
      (det_scale_left v a b))
    apply Fraction.equiv_trans (Fraction.add_comm _ _)
    apply Fraction.equiv_trans (Fraction.add_zero _)
    have he : Fraction.equiv (Fraction.mul v (det b a))
        (Fraction.mul (Fraction.quotient (det p a) (det a b) hd) (det a b)) := by
      apply Fraction.equiv_trans (Fraction.mul_equiv_left v (det_swap_neg b a))
      simp only [v,negF,Fraction.quotient,Fraction.equiv,Fraction.mul,Int.neg_mul,Int.mul_neg,
        Int.neg_neg]
    exact Fraction.equiv_trans he (quotient_mul (det p a) (det a b) hd)

theorem det_vertical (p : Point) :
    Fraction.equiv (det p (Fraction.ofInt 0,Fraction.ofInt 1)) p.1 := by
  simp only [det,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.neg_zero,Int.add_zero]
  ac_nf

/-- Collinearity with a positive horizontal ray derives the scale factor;
the point need not itself be in the positive half-plane. -/
theorem collinear_scale (p q : Point) (hq : 0 < q.1.num)
    (hd : Fraction.equiv (det p q) (Fraction.ofInt 0)) :
    pointEquiv p (pointScale (Fraction.quotient p.1 q.1 hq) q) := by
  let e : Point := (Fraction.ofInt 0,Fraction.ofInt 1)
  let w := Fraction.quotient p.1 q.1 hq
  have hn : (det q e).num ≠ 0 := by
    simp only [e,det,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.neg_zero,Int.add_zero]
    exact Int.ne_of_gt (Int.mul_pos hq q.2.den_pos)
  apply det_coordinates_injective q e hn
  · exact Fraction.equiv_trans (det_vertical p)
      (Fraction.equiv_trans (Fraction.equiv_symm (quotient_mul p.1 q.1 hq))
        (Fraction.equiv_symm (det_vertical (pointScale w q))))
  · exact Fraction.equiv_trans hd (Fraction.equiv_symm
      (Fraction.equiv_trans (det_scale_left w q q)
        (Fraction.equiv_trans (Fraction.mul_equiv_left w (det_self q)) (Fraction.mul_zero w))))

/-- A collinear filled triangle is a radial segment when the second
endpoint bounds the first horizontally. Its collapse is derived from the
barycentric membership, not supplied as set agreement. -/
theorem triangle_collinear_radial (a b x : Point) (ha : 0 ≤ a.1.num) (hb : 0 < b.1.num)
    (hab : Fraction.le a.1 b.1)
    (hd : Fraction.equiv (det a b) (Fraction.ofInt 0))
    (hx : Triangle a b x) :
    ∃ w, UnitInterval w ∧ pointEquiv x (pointScale w b) := by
  obtain ⟨u,v,hu,hv,hs,he⟩ := hx
  have hxdet : Fraction.equiv (det x b) (Fraction.ofInt 0) := by
    apply Fraction.equiv_trans (det_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
    apply Fraction.equiv_trans (det_add_left b _ _)
    apply Fraction.equiv_trans (Fraction.add_equiv
      (Fraction.equiv_trans (det_scale_left u b a)
        (Fraction.equiv_trans (Fraction.mul_equiv_left u hd) (Fraction.mul_zero u)))
      (Fraction.equiv_trans (det_scale_left v b b)
        (Fraction.equiv_trans (Fraction.mul_equiv_left v (det_self b)) (Fraction.mul_zero v))))
    exact Fraction.add_zero _
  have hupper : Fraction.le x.1 b.1 := by
    apply Fraction.le_equiv_left he.1
    apply Fraction.magnitudes.le_trans (Fraction.add_le_add
      (Fraction.mul_le_mul_nonnegative_left hab u hu) (Fraction.magnitudes.le_refl _))
    apply Fraction.le_equiv_left (Fraction.equiv_symm (Fraction.add_mul u v b.1))
    exact Fraction.le_equiv_right
      (Fraction.mul_le_mul_nonnegative hs b.1 (Int.le_of_lt hb))
      (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one])
  have hlower : 0 ≤ x.1.num := by
    exact Fraction.nonnegative_equiv he.1 (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _ hu ha) (Fraction.nonnegative_mul _ _ hv (Int.le_of_lt hb)))
  let w := Fraction.quotient x.1 b.1 hb
  refine ⟨w,⟨Int.mul_nonneg hlower (Int.le_of_lt b.1.den_pos),?_⟩,collinear_scale x b hb hxdet⟩
  change x.1.num*b.1.den ≤ x.1.den*b.1.num
  simpa only [Fraction.le,Int.mul_comm] using hupper

/-- A residual barycentric coordinate, with its nonnegativity checked by
the simplex-exit inequalities rather than built into its definition. -/
def residual (x t p : Fraction) : Fraction := durationDifference (Fraction.mul t p) x

theorem residuals_total (s v u w t : Fraction) :
    Fraction.equiv (Fraction.add (Fraction.add
      (residual (durationDifference (Fraction.add s v) (Fraction.ofInt 1)) t
        (durationDifference (Fraction.add u w) (Fraction.ofInt 1)))
      (residual s t u)) (residual v t w)) (complement t) := by
  simp only [residual,durationDifference,negF,complement,Fraction.equiv,Fraction.add,Fraction.mul,
    Fraction.ofInt,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.sub_mul,Int.mul_sub,
    Int.one_mul,Int.mul_one,Int.neg_add,Int.neg_neg]
  ac_nf
  omega

theorem residuals_decomposition (a b : Point) (s v u w t : Fraction) :
    pointEquiv (pointAdd (pointScale s a) (pointScale v b))
      (pointAdd (pointScale t (pointAdd (pointScale u a) (pointScale w b)))
        (pointAdd (pointScale (residual s t u) a) (pointScale (residual v t w) b))) := by
  constructor <;>
    simp only [residual,durationDifference,negF,pointAdd,pointScale,Fraction.equiv,Fraction.add,
      Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

theorem barycentric_total (u v : Fraction) :
    Fraction.equiv (Fraction.add (Fraction.add
      (durationDifference (Fraction.add u v) (Fraction.ofInt 1)) u) v) (Fraction.ofInt 1) := by
  simp only [durationDifference,negF,Fraction.equiv,Fraction.add,Fraction.ofInt,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one]
  ac_nf
  omega

theorem residual_zero (x t p : Fraction) (he : Fraction.equiv (Fraction.mul t p) x) :
    Fraction.equiv (residual x t p) (Fraction.ofInt 0) := by
  apply Fraction.equiv_trans (difference_congr he (Fraction.equiv_refl x))
  simp only [durationDifference,negF,Fraction.equiv,Fraction.add,Fraction.ofInt,
    Int.neg_mul,Int.mul_one,Int.zero_mul]
  omega

theorem remaining_weight (u v w : Fraction)
    (hs : Fraction.equiv (Fraction.add u (Fraction.add v w)) (Fraction.ofInt 1)) :
    Fraction.equiv u (durationDifference (Fraction.add v w) (Fraction.ofInt 1)) := by
  have he : Fraction.equiv
      (durationDifference (Fraction.add v w) (Fraction.add u (Fraction.add v w))) u := by
    simp only [durationDifference,negF,Fraction.equiv,Fraction.add,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf
    omega
  exact Fraction.equiv_trans (Fraction.equiv_symm he)
    (difference_congr (Fraction.equiv_refl _) hs)

theorem weights_pair_bound (u v w : Fraction) (hu : 0 ≤ u.num)
    (hs : Fraction.equiv (Fraction.add u (Fraction.add v w)) (Fraction.ofInt 1)) :
    Fraction.le (Fraction.add v w) (Fraction.ofInt 1) :=
  Fraction.le_equiv_right (Fraction.le_equiv_right
    (Fraction.le_add_nonnegative (Fraction.add v w) u hu) (Fraction.add_comm _ _)) hs

theorem triangleAt_of_weights (a b c x : Point) (u v w : Fraction)
    (hu : 0 ≤ u.num) (hv : 0 ≤ v.num) (hw : 0 ≤ w.num)
    (hs : Fraction.equiv (Fraction.add u (Fraction.add v w)) (Fraction.ofInt 1))
    (he : pointEquiv x (pointAdd (pointScale u a)
      (pointAdd (pointScale v b) (pointScale w c)))) : TriangleAt a b c x := by
  refine ⟨v,w,hv,hw,weights_pair_bound u v w hu hs,?_⟩
  apply pointEquiv_trans (pointSub_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
  apply pointEquiv_trans (pointSub_congr
    (pointAdd_congr (pointScale_ratio_congr (remaining_weight u v w hs)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
  constructor <;>
    simp only [durationDifference,negF,pointSub,pointNeg,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,Int.add_mul,Int.mul_add,
      Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one] <;> ac_nf <;> omega

/-- Exchange for a point with explicitly derived coordinates in the original
two directions. Signed coordinates of the inserted vertex are allowed. -/
theorem exchange_of_coordinates (a b p x : Point) (u w : Fraction)
    (hp : pointEquiv p (pointAdd (pointScale u a) (pointScale w b)))
    (hx : Triangle a b x) :
    Triangle a p x ∨ TriangleAt a p b x ∨ Triangle p b x := by
  obtain ⟨s,v,hs,hv,hsv,he⟩ := hx
  let x0 := durationDifference (Fraction.add s v) (Fraction.ofInt 1)
  let p0 := durationDifference (Fraction.add u w) (Fraction.ofInt 1)
  obtain ⟨tRat,htRat,_,h0Rat,h1Rat,h2Rat,hfaceRat⟩ :=
    SimplexExit.simplex_exit x0.toRat s.toRat v.toRat p0.toRat u.toRat w.toRat
      ((Fraction.nonnegative_iff_toRat _).mp ((difference_nonnegative_iff _ _).mpr hsv))
      ((Fraction.nonnegative_iff_toRat _).mp hs) ((Fraction.nonnegative_iff_toRat _).mp hv)
      (by simpa only [Fraction.equiv_iff_toRat, Fraction.toRat_add, Fraction.toRat_ofInt,
        Rat.intCast_one] using! (barycentric_total s v))
      (by simpa only [Fraction.equiv_iff_toRat, Fraction.toRat_add, Fraction.toRat_ofInt,
        Rat.intCast_one] using! (barycentric_total u w))
  let t := Fraction.ofRat tRat
  have ht : 0 ≤ t.num := (Fraction.nonnegative_iff_toRat t).mpr
    (by simpa only [t, Fraction.toRat_ofRat] using htRat)
  have h0 : Fraction.le (Fraction.mul t p0) x0 := (Fraction.le_iff_toRat _ _).mpr
    (by simpa only [t, Fraction.toRat_mul, Fraction.toRat_ofRat] using h0Rat)
  have h1 : Fraction.le (Fraction.mul t u) s := (Fraction.le_iff_toRat _ _).mpr
    (by simpa only [t, Fraction.toRat_mul, Fraction.toRat_ofRat] using h1Rat)
  have h2 : Fraction.le (Fraction.mul t w) v := (Fraction.le_iff_toRat _ _).mpr
    (by simpa only [t, Fraction.toRat_mul, Fraction.toRat_ofRat] using h2Rat)
  have hface : Fraction.equiv (Fraction.mul t p0) x0 ∨
      Fraction.equiv (Fraction.mul t u) s ∨ Fraction.equiv (Fraction.mul t w) v := by
    simpa only [Fraction.equiv_iff_toRat, t, Fraction.toRat_mul, Fraction.toRat_ofRat]
      using hfaceRat
  let r0 := residual x0 t p0
  let r1 := residual s t u
  let r2 := residual v t w
  have hr0 : 0 ≤ r0.num := (difference_nonnegative_iff _ _).mpr h0
  have hr1 : 0 ≤ r1.num := (difference_nonnegative_iff _ _).mpr h1
  have hr2 : 0 ≤ r2.num := (difference_nonnegative_iff _ _).mpr h2
  have htotal : Fraction.equiv (Fraction.add (Fraction.add (Fraction.add r0 r1) r2) t)
      (Fraction.ofInt 1) := Fraction.equiv_trans
    (Fraction.add_equiv_right t (residuals_total s v u w t)) (weights_sum_one t)
  have hx' : pointEquiv x (pointAdd (pointScale t p)
      (pointAdd (pointScale r1 a) (pointScale r2 b))) :=
    pointEquiv_trans he (pointEquiv_trans (residuals_decomposition a b s v u w t)
      (pointAdd_congr (pointScale_congr t (pointEquiv_symm hp))
        ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩))
  rcases hface with hz | hz | hz
  · have hr : Fraction.equiv r0 (Fraction.ofInt 0) := residual_zero x0 t p0 hz
    have hnum : r0.num=0 := by simpa only [Fraction.equiv,Fraction.ofInt,Int.mul_one,Int.zero_mul] using hr
    have hsum : Fraction.equiv (Fraction.add r1 (Fraction.add t r2)) (Fraction.ofInt 1) := by
      apply Fraction.equiv_trans (b := Fraction.add (Fraction.add (Fraction.add r0 r1) r2) t) ?_ htotal
      simp only [Fraction.equiv,Fraction.add,hnum,Int.zero_mul,Int.zero_add,
        Int.add_mul,Int.mul_add]
      ac_nf
    right; left
    apply triangleAt_of_weights a p b x r1 t r2 hr1 ht hr2 hsum
    apply pointEquiv_trans hx'
    constructor <;> simp only [pointAdd,Fraction.equiv,Fraction.add,Int.add_mul,Int.mul_add] <;> ac_nf
  · have hr : Fraction.equiv r1 (Fraction.ofInt 0) := residual_zero s t u hz
    have hnum : r1.num=0 := by simpa only [Fraction.equiv,Fraction.ofInt,Int.mul_one,Int.zero_mul] using hr
    have hsum : Fraction.equiv (Fraction.add r0 (Fraction.add t r2)) (Fraction.ofInt 1) := by
      apply Fraction.equiv_trans (b := Fraction.add (Fraction.add (Fraction.add r0 r1) r2) t) ?_ htotal
      simp only [Fraction.equiv,Fraction.add,hnum,Int.zero_mul,Int.add_zero,
        Int.add_mul,Int.mul_add]
      ac_nf
    right; right
    refine ⟨t,r2,ht,hr2,weights_pair_bound r0 t r2 hr0 hsum,?_⟩
    apply pointEquiv_trans hx'
    constructor <;> simp only [pointScale,pointAdd,Fraction.equiv,Fraction.add,Fraction.mul,hnum,
      Int.zero_mul,Int.zero_add,Int.add_mul,Int.mul_add] <;> ac_nf
  · have hr : Fraction.equiv r2 (Fraction.ofInt 0) := residual_zero v t w hz
    have hnum : r2.num=0 := by simpa only [Fraction.equiv,Fraction.ofInt,Int.mul_one,Int.zero_mul] using hr
    have hsum : Fraction.equiv (Fraction.add r0 (Fraction.add r1 t)) (Fraction.ofInt 1) := by
      apply Fraction.equiv_trans (b := Fraction.add (Fraction.add (Fraction.add r0 r1) r2) t) ?_ htotal
      simp only [Fraction.equiv,Fraction.add,hnum,Int.zero_mul,Int.add_zero,
        Int.add_mul,Int.mul_add]
      ac_nf
    left
    refine ⟨r1,t,hr1,ht,weights_pair_bound r0 r1 t hr0 hsum,?_⟩
    apply pointEquiv_trans hx'
    constructor <;> simp only [pointScale,pointAdd,Fraction.equiv,Fraction.add,Fraction.mul,hnum,
      Int.zero_mul,Int.add_zero,Int.add_mul,Int.mul_add] <;> ac_nf

/-- The independent-direction case of finite triangle exchange, with the
inserted point's coordinates derived, rather than supplied nonnegative. -/
theorem exchange_independent (a b p x : Point) (hd : 0 < (det a b).num)
    (hx : Triangle a b x) :
    Triangle a p x ∨ TriangleAt a p b x ∨ Triangle p b x :=
  exchange_of_coordinates a b p x _ _ (coordinates a b p hd) hx

theorem triangle_radial_endpoint (a b x : Point) (w : Fraction)
    (hw : UnitInterval w) (he : pointEquiv x (pointScale w b)) : Triangle a b x := by
  refine ⟨Fraction.ofInt 0,w,by decide,hw.1,?_,?_⟩
  · simpa only [Fraction.le,Fraction.add,Fraction.ofInt,Int.zero_mul,Int.mul_one,
      Int.one_mul,Int.zero_add] using hw.2
  · apply pointEquiv_trans he
    constructor <;> simp only [pointScale,pointAdd,Fraction.equiv,Fraction.mul,Fraction.add,
      Fraction.ofInt,Int.zero_mul,Int.zero_add,Int.one_mul,Int.mul_one] <;> ac_nf

/-- Finite triangle exchange in the positive horizontal chart, including
collinear and coincident original rays. The inserted vertex is arbitrary.
This is a set inclusion, without an assigned area or a limiting premise. -/
theorem exchange_positive (a b p x : Point) (ha : 0 < a.1.num) (hb : 0 < b.1.num)
    (hd : 0 ≤ (det a b).num) (hx : Triangle a b x) :
    Triangle a p x ∨ TriangleAt a p b x ∨ Triangle p b x := by
  by_cases hpos : 0 < (det a b).num
  · exact exchange_independent a b p x hpos hx
  · have hnum : (det a b).num=0 := by omega
    have hz : Fraction.equiv (det a b) (Fraction.ofInt 0) := by
      simp only [Fraction.equiv,Fraction.ofInt,hnum,Int.zero_mul,Int.mul_zero]
    by_cases hab : Fraction.le a.1 b.1
    · obtain ⟨w,hw,he⟩ := triangle_collinear_radial a b x (Int.le_of_lt ha) hb hab hz hx
      exact Or.inr (Or.inr (triangle_radial_endpoint p b x w hw he))
    · have hba : Fraction.le b.1 a.1 := by unfold Fraction.le at *; omega
      have hz' : Fraction.equiv (det b a) (Fraction.ofInt 0) :=
        Fraction.equiv_trans (det_swap_neg b a) (by
          simp only [negF,Fraction.equiv,Fraction.ofInt,hnum,Int.neg_zero,Int.zero_mul,Int.mul_zero])
      obtain ⟨w,hw,he⟩ := triangle_collinear_radial b a x (Int.le_of_lt hb) ha hba hz'
        ((triangle_swap a b x).mp hx)
      exact Or.inl ((triangle_swap p a x).mp (triangle_radial_endpoint p a x w hw he))

/-- A translated filled triangle is a convex combination of its base and
an arbitrary point on the opposite edge. The parameters are derived. -/
theorem triangleAt_radial (a b c x : Point) (hx : TriangleAt a b c x) :
    ∃ r u, UnitInterval r ∧ UnitInterval u ∧
      pointEquiv x (lerp r a (lerp u b c)) := by
  obtain ⟨r,u,hr,hu,he⟩ := (RadialSector.triangle_radial _ _ _).mp hx
  refine ⟨r,u,hr,hu,?_⟩
  have hi : pointEquiv x (pointAdd a (pointSub x a)) := by
    constructor <;> simp only [pointSub,pointNeg,pointAdd,Fraction.equiv,Fraction.add,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega
  apply pointEquiv_trans hi
  apply pointEquiv_trans (pointAdd_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ he)
  constructor <;> simp only [lerp,complement,pointSub,pointNeg,pointAdd,pointScale,
    Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub,
    Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

/-- Enclose an actual translated triangle from three endpoint bounds.
No membership in an already bounded patch is assumed. -/
theorem triangleAt_square (a b c x anchor : Point) (R : Fraction)
    (ha : Fraction.le (PointBounds.pointNorm (pointSub a anchor)) R)
    (hb : Fraction.le (PointBounds.pointNorm (pointSub b anchor)) R)
    (hc : Fraction.le (PointBounds.pointNorm (pointSub c anchor)) R)
    (hx : TriangleAt a b c x) : SquareContains anchor R x := by
  obtain ⟨r,u,hr,hu,he⟩ := triangleAt_radial a b c x hx
  exact (square_contains_congr anchor R he).mpr (ball_inside_square anchor _ R
    (lerp_ball_bound r hr anchor a _ R ha (lerp_ball_bound u hu anchor b c R hb hc)))

/-- With a common start, every point of the translated connector triangle
has rational matched-edge parameters. This special triangular case does not
assert that every four-vertex strip is a rational matched patch. -/
theorem triangleAt_common_start_patch (a p q x : Point) (hx : TriangleAt a p q x) :
    ∃ r u, UnitInterval r ∧ UnitInterval u ∧
      pointEquiv x (matchedPatch r u a p a q) := by
  obtain ⟨r,u,hr,hu,he⟩ := triangleAt_radial a p q x hx
  refine ⟨r,u,hr,hu,pointEquiv_trans he ?_⟩
  constructor <;> simp only [matchedPatch,lerp,complement,pointAdd,pointScale,Fraction.equiv,
    Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub] <;> ac_nf <;> omega

/-- One-cell geometric difference inclusion. A point in the sampled sector
but outside the mechanical sector lies in the actual enclosing square or
the terminal radial connector. This is not the many-cell collar theorem. -/
theorem one_cell_difference_cover (a p q x anchor : Point) (R : Fraction)
    (ha : 0 < a.1.num) (hq : 0 < q.1.num) (hd : 0 ≤ (det a q).num)
    (hba : Fraction.le (PointBounds.pointNorm (pointSub a anchor)) R)
    (hbp : Fraction.le (PointBounds.pointNorm (pointSub p anchor)) R)
    (hbq : Fraction.le (PointBounds.pointNorm (pointSub q anchor)) R)
    (hx : Triangle a q x) (hn : ¬ Triangle a p x) :
    SquareContains anchor R x ∨ Triangle p q x := by
  rcases exchange_positive a q p x ha hq hd hx with hp | hp | hp
  · exact False.elim (hn hp)
  · exact Or.inl (triangleAt_square a p q x anchor R hba hbp hbq hp)
  · exact Or.inr hp

end NewtonLimitDynamics.Polygon.TriangleExchange
