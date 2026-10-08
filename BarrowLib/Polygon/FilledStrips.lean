import BarrowLib.Polygon.TriangleExchange

/-! Convexity of the filled paired-edge strip with independent rational
parameters on its two edges. Source: the original English statements and
checked rational-coordinate derivations here. This is project proof
provenance, without a claim of historical textual support, discovery or
priority. The two group weights may vanish; no nondegeneracy or positive
area is assumed. Only Barrow/Classics mathematical dependencies are used.
-/

namespace NewtonLimitDynamics.Polygon.FilledStrips
open NewtonLimitDynamics TimeSubdivision ConvexCover SupportingTangents

private def zero : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1

def FilledCell (p0 p1 q0 q1 x : Point) : Prop :=
  ∃ theta mu lambda : Fraction,
    UnitInterval theta ∧ UnitInterval mu ∧ UnitInterval lambda ∧
    pointEquiv x (filledPatch theta mu lambda p0 p1 q0 q1)

private theorem nonneg_le_one (a : Fraction) (ha : 0 ≤ a.num)
    (h : Fraction.le a one) : UnitInterval a := by
  refine ⟨ha,?_⟩
  simpa only [one,Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using h

private theorem zero_le (a : Fraction) (h : 0 ≤ a.num) : Fraction.le zero a := by
  simpa only [zero,Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using h

private theorem pair_split (a b : Fraction) (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    ∃ theta : Fraction, UnitInterval theta ∧
      Fraction.equiv (Fraction.mul (complement theta) (Fraction.add a b)) a ∧
      Fraction.equiv (Fraction.mul theta (Fraction.add a b)) b := by
  let S := Fraction.add a b
  have h0 : Fraction.le zero b := zero_le b hb
  have h1 : Fraction.le b S :=
    Fraction.le_equiv_right (Fraction.le_add_nonnegative b a ha) (Fraction.add_comm b a)
  obtain ⟨theta,ht,he⟩ := RadialSector.interval_parameter zero S b h0 h1
  have hr : Fraction.equiv (Fraction.mul theta S) b := by
    have hz : Fraction.equiv (affine theta zero S) (Fraction.mul theta S) := by
      simp only [affine,zero,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        complement,Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add]
      ac_nf
    exact Fraction.equiv_trans (Fraction.equiv_symm hz) he
  refine ⟨theta,ht,?_,hr⟩
  have hs : Fraction.equiv
      (Fraction.add (Fraction.mul (complement theta) S) (Fraction.mul theta S)) S := by
    exact Fraction.equiv_trans (Fraction.equiv_symm (Fraction.add_mul _ _ _))
      (Fraction.equiv_trans (Fraction.mul_equiv_right S (weights_sum_one theta))
        (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]))
  have heq : Fraction.equiv
      (Fraction.add (Fraction.mul (complement theta) S) b) (Fraction.add a b) :=
    Fraction.equiv_trans (Fraction.add_equiv_left _ (Fraction.equiv_symm hr))
      (Fraction.equiv_trans hs (Fraction.equiv_refl S))
  have hc : Fraction.equiv
      (Fraction.add b (Fraction.mul (complement theta) S)) (Fraction.add b a) :=
    Fraction.equiv_trans (Fraction.equiv_symm (Fraction.add_comm _ _))
      (Fraction.equiv_trans heq (Fraction.add_comm _ _))
  have hleft : Fraction.le (Fraction.mul (complement theta) S) a :=
    Fraction.le_add_cancel_left b _ _ (Fraction.le_of_equiv hc)
  have hright : Fraction.le a (Fraction.mul (complement theta) S) := by
    exact Fraction.le_add_cancel_left b _ _
      (Fraction.le_of_equiv (Fraction.equiv_symm hc))
  exact (Fraction.equiv_iff_mutual_le _ _).mpr ⟨hleft,hright⟩

private def weightedPoint (w0 w1 w2 w3 : Fraction)
    (p0 p1 q0 q1 : Point) : Point :=
  pointAdd (pointAdd (pointScale w0 p0) (pointScale w1 p1))
    (pointAdd (pointScale w2 q0) (pointScale w3 q1))

private def FourWeights (p0 p1 q0 q1 x : Point) : Prop :=
  ∃ w0 w1 w2 w3 : Fraction,
    0 ≤ w0.num ∧ 0 ≤ w1.num ∧ 0 ≤ w2.num ∧ 0 ≤ w3.num ∧
    Fraction.equiv (Fraction.add (Fraction.add w0 w1) (Fraction.add w2 w3)) one ∧
    pointEquiv x (weightedPoint w0 w1 w2 w3 p0 p1 q0 q1)

private theorem patch_weights (theta mu lambda : Fraction) (p0 p1 q0 q1 : Point) :
    pointEquiv (filledPatch theta mu lambda p0 p1 q0 q1)
      (weightedPoint
        (Fraction.mul (complement lambda) (complement theta))
        (Fraction.mul (complement lambda) theta)
        (Fraction.mul lambda (complement mu))
        (Fraction.mul lambda mu) p0 p1 q0 q1) := by
  constructor <;>
    simp only [filledPatch,weightedPoint,lerp,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add] <;>
    ac_nf

private theorem patch_weights_total (theta mu lambda : Fraction) :
    Fraction.equiv
      (Fraction.add
        (Fraction.add
          (Fraction.mul (complement lambda) (complement theta))
          (Fraction.mul (complement lambda) theta))
        (Fraction.add
          (Fraction.mul lambda (complement mu))
          (Fraction.mul lambda mu))) one := by
  simp only [complement,one,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub]
  ac_nf
  omega

private theorem patch_four_weights (p0 p1 q0 q1 x : Point)
    (h : FilledCell p0 p1 q0 q1 x) : FourWeights p0 p1 q0 q1 x := by
  obtain ⟨theta,mu,lambda,ht,hm,hl,hx⟩ := h
  refine ⟨Fraction.mul (complement lambda) (complement theta),
    Fraction.mul (complement lambda) theta,
    Fraction.mul lambda (complement mu),Fraction.mul lambda mu,
    Fraction.nonnegative_mul _ _ (complement_nonnegative lambda hl) (complement_nonnegative theta ht),
    Fraction.nonnegative_mul _ _ (complement_nonnegative lambda hl) ht.1,
    Fraction.nonnegative_mul _ _ hl.1 (complement_nonnegative mu hm),
    Fraction.nonnegative_mul _ _ hl.1 hm.1,
    patch_weights_total theta mu lambda,pointEquiv_trans hx (patch_weights theta mu lambda p0 p1 q0 q1)⟩

private theorem add_right_cancel_equiv (a b c : Fraction)
    (h : Fraction.equiv (Fraction.add a c) (Fraction.add b c)) :
    Fraction.equiv a b := by
  have hc : Fraction.equiv (Fraction.add c a) (Fraction.add c b) :=
    Fraction.equiv_trans (Fraction.add_comm c a)
      (Fraction.equiv_trans h (Fraction.add_comm b c))
  exact (Fraction.equiv_iff_mutual_le a b).mpr
    ⟨Fraction.le_add_cancel_left c a b (Fraction.le_of_equiv hc),
     Fraction.le_add_cancel_left c b a (Fraction.le_of_equiv (Fraction.equiv_symm hc))⟩

private theorem weightedPoint_congr (w0 w1 w2 w3 v0 v1 v2 v3 : Fraction)
    (p0 p1 q0 q1 : Point)
    (h0 : Fraction.equiv w0 v0) (h1 : Fraction.equiv w1 v1)
    (h2 : Fraction.equiv w2 v2) (h3 : Fraction.equiv w3 v3) :
    pointEquiv (weightedPoint w0 w1 w2 w3 p0 p1 q0 q1)
      (weightedPoint v0 v1 v2 v3 p0 p1 q0 q1) :=
  pointAdd_congr
    (pointAdd_congr
      (pointScale_ratio_congr h0 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (pointScale_ratio_congr h1 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩))
    (pointAdd_congr
      (pointScale_ratio_congr h2 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (pointScale_ratio_congr h3 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩))

private theorem four_weights_patch (p0 p1 q0 q1 x : Point)
    (h : FourWeights p0 p1 q0 q1 x) : FilledCell p0 p1 q0 q1 x := by
  obtain ⟨w0,w1,w2,w3,h0,h1,h2,h3,htotal,hx⟩ := h
  let Wp := Fraction.add w0 w1
  let Wq := Fraction.add w2 w3
  have hWp : 0 ≤ Wp.num := Fraction.nonnegative_add _ _ h0 h1
  have hWq : 0 ≤ Wq.num := Fraction.nonnegative_add _ _ h2 h3
  have hlamle : Fraction.le Wq one :=
    Fraction.le_equiv_right
      (Fraction.le_equiv_right (Fraction.le_add_nonnegative Wq Wp hWp)
        (Fraction.add_comm Wq Wp)) htotal
  have hlam : UnitInterval Wq := nonneg_le_one Wq hWq hlamle
  obtain ⟨theta,hθ,hθ0,hθ1⟩ := pair_split w0 w1 h0 h1
  obtain ⟨mu,hμ,hμ0,hμ1⟩ := pair_split w2 w3 h2 h3
  have hcomp : Fraction.equiv (complement Wq) Wp :=
    add_right_cancel_equiv (complement Wq) Wp Wq
      (Fraction.equiv_trans (weights_sum_one Wq) (Fraction.equiv_symm htotal))
  have hw0 : Fraction.equiv (Fraction.mul (complement Wq) (complement theta)) w0 :=
    Fraction.equiv_trans (Fraction.mul_equiv_right (complement theta) hcomp)
      (Fraction.equiv_trans (Fraction.mul_comm Wp (complement theta)) hθ0)
  have hw1 : Fraction.equiv (Fraction.mul (complement Wq) theta) w1 :=
    Fraction.equiv_trans (Fraction.mul_equiv_right theta hcomp)
      (Fraction.equiv_trans (Fraction.mul_comm Wp theta) hθ1)
  have hw2 : Fraction.equiv (Fraction.mul Wq (complement mu)) w2 :=
    Fraction.equiv_trans (Fraction.mul_comm Wq (complement mu)) hμ0
  have hw3 : Fraction.equiv (Fraction.mul Wq mu) w3 :=
    Fraction.equiv_trans (Fraction.mul_comm Wq mu) hμ1
  refine ⟨theta,mu,Wq,hθ,hμ,hlam,pointEquiv_trans hx (pointEquiv_symm ?_)⟩
  exact pointEquiv_trans (patch_weights theta mu Wq p0 p1 q0 q1)
    (weightedPoint_congr _ _ _ _ _ _ _ _ p0 p1 q0 q1 hw0 hw1 hw2 hw3)

private def blend (r a b : Fraction) : Fraction :=
  Fraction.add (Fraction.mul (complement r) a) (Fraction.mul r b)

private theorem blend_nonneg (r a b : Fraction) (hr : UnitInterval r)
    (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) : 0 ≤ (blend r a b).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ (complement_nonnegative r hr) ha)
    (Fraction.nonnegative_mul _ _ hr.1 hb)

private theorem blend_equiv (r a b c d : Fraction)
    (hac : Fraction.equiv a c) (hbd : Fraction.equiv b d) :
    Fraction.equiv (blend r a b) (blend r c d) :=
  Fraction.add_equiv
    (Fraction.mul_equiv_left (complement r) hac)
    (Fraction.mul_equiv_left r hbd)

private theorem blend_total (r a0 a1 a2 a3 b0 b1 b2 b3 : Fraction)
    (ha : Fraction.equiv (Fraction.add (Fraction.add a0 a1) (Fraction.add a2 a3)) one)
    (hb : Fraction.equiv (Fraction.add (Fraction.add b0 b1) (Fraction.add b2 b3)) one) :
    Fraction.equiv
      (Fraction.add (Fraction.add (blend r a0 b0) (blend r a1 b1))
        (Fraction.add (blend r a2 b2) (blend r a3 b3))) one := by
  have hdist : Fraction.equiv
      (Fraction.add (Fraction.add (blend r a0 b0) (blend r a1 b1))
        (Fraction.add (blend r a2 b2) (blend r a3 b3)))
      (blend r (Fraction.add (Fraction.add a0 a1) (Fraction.add a2 a3))
        (Fraction.add (Fraction.add b0 b1) (Fraction.add b2 b3))) := by
    simp only [blend,complement,Fraction.equiv,Fraction.add,Fraction.mul,
      Int.add_mul,Int.mul_add,Int.sub_mul,Int.mul_sub]
    ac_nf
  exact Fraction.equiv_trans hdist
    (Fraction.equiv_trans (blend_equiv r _ _ one one ha hb)
      (RadialSector.affine_constant r one))

private theorem weightedPoint_blend (r a0 a1 a2 a3 b0 b1 b2 b3 : Fraction)
    (p0 p1 q0 q1 : Point) :
    pointEquiv
      (lerp r (weightedPoint a0 a1 a2 a3 p0 p1 q0 q1)
        (weightedPoint b0 b1 b2 b3 p0 p1 q0 q1))
      (weightedPoint (blend r a0 b0) (blend r a1 b1)
        (blend r a2 b2) (blend r a3 b3) p0 p1 q0 q1) := by
  constructor <;>
    simp only [weightedPoint,blend,lerp,complement,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,
      Int.sub_mul,Int.mul_sub] <;>
    ac_nf

private theorem lerp_congr (r : Fraction) {a b c d : Point}
    (hac : pointEquiv a c) (hbd : pointEquiv b d) :
    pointEquiv (lerp r a b) (lerp r c d) :=
  pointAdd_congr (pointScale_congr (complement r) hac) (pointScale_congr r hbd)

private theorem four_weights_convex (p0 p1 q0 q1 x y : Point)
    (r : Fraction) (hr : UnitInterval r)
    (hx : FourWeights p0 p1 q0 q1 x) (hy : FourWeights p0 p1 q0 q1 y) :
    FourWeights p0 p1 q0 q1 (lerp r x y) := by
  obtain ⟨a0,a1,a2,a3,ha0,ha1,ha2,ha3,hatotal,hax⟩ := hx
  obtain ⟨b0,b1,b2,b3,hb0,hb1,hb2,hb3,hbtotal,hby⟩ := hy
  refine ⟨blend r a0 b0,blend r a1 b1,blend r a2 b2,blend r a3 b3,
    blend_nonneg r a0 b0 hr ha0 hb0,blend_nonneg r a1 b1 hr ha1 hb1,
    blend_nonneg r a2 b2 hr ha2 hb2,blend_nonneg r a3 b3 hr ha3 hb3,
    blend_total r a0 a1 a2 a3 b0 b1 b2 b3 hatotal hbtotal,?_⟩
  exact pointEquiv_trans (lerp_congr r hax hby)
    (weightedPoint_blend r a0 a1 a2 a3 b0 b1 b2 b3 p0 p1 q0 q1)

/-- The rational four-vertex filled cell is closed under convex interpolation.
This includes zero groups, repeated vertices, and parallel edges. -/
theorem filledCell_convex (p0 p1 q0 q1 x y : Point)
    (r : Fraction) (hr : UnitInterval r)
    (hx : FilledCell p0 p1 q0 q1 x) (hy : FilledCell p0 p1 q0 q1 y) :
    FilledCell p0 p1 q0 q1 (lerp r x y) :=
  four_weights_patch p0 p1 q0 q1 _
    (four_weights_convex p0 p1 q0 q1 x y r hr
      (patch_four_weights p0 p1 q0 q1 x hx)
      (patch_four_weights p0 p1 q0 q1 y hy))

theorem filledCell_congr (p0 p1 q0 q1 x y : Point)
    (hxy : pointEquiv x y) (hy : FilledCell p0 p1 q0 q1 y) :
    FilledCell p0 p1 q0 q1 x := by
  obtain ⟨theta,mu,lambda,ht,hm,hl,he⟩ := hy
  exact ⟨theta,mu,lambda,ht,hm,hl,pointEquiv_trans hxy he⟩

theorem p_edge (p0 p1 q0 q1 : Point) (theta : Fraction)
    (ht : UnitInterval theta) :
    FilledCell p0 p1 q0 q1 (lerp theta p0 p1) := by
  refine ⟨theta,zero,zero,ht,⟨by decide,by decide⟩,
    ⟨by decide,by decide⟩,?_⟩
  constructor <;>
    simp only [filledPatch,lerp,complement,zero,Fraction.ofInt,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,
      Int.sub_mul,Int.mul_sub,Int.zero_mul,Int.mul_zero,Int.one_mul,
      Int.mul_one,Int.zero_add,Int.add_zero] <;>
    ac_nf <;> omega

theorem q_edge (p0 p1 q0 q1 : Point) (mu : Fraction)
    (hm : UnitInterval mu) :
    FilledCell p0 p1 q0 q1 (lerp mu q0 q1) := by
  refine ⟨zero,mu,one,⟨by decide,by decide⟩,hm,
    ⟨by decide,by decide⟩,?_⟩
  constructor <;>
    simp only [filledPatch,lerp,complement,zero,one,Fraction.ofInt,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,
      Int.sub_mul,Int.mul_sub,Int.zero_mul,Int.mul_zero,Int.one_mul,
      Int.mul_one,Int.zero_add,Int.add_zero] <;>
    ac_nf <;> omega

theorem start_connector (p0 p1 q0 q1 : Point) (lambda : Fraction)
    (hl : UnitInterval lambda) :
    FilledCell p0 p1 q0 q1 (lerp lambda p0 q0) := by
  refine ⟨zero,zero,lambda,⟨by decide,by decide⟩,
    ⟨by decide,by decide⟩,hl,?_⟩
  constructor <;>
    simp only [filledPatch,lerp,complement,zero,Fraction.ofInt,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,
      Int.sub_mul,Int.mul_sub,Int.zero_mul,Int.mul_zero,Int.one_mul,
      Int.mul_one,Int.zero_add,Int.add_zero] <;>
    ac_nf <;> omega

theorem end_connector (p0 p1 q0 q1 : Point) (lambda : Fraction)
    (hl : UnitInterval lambda) :
    FilledCell p0 p1 q0 q1 (lerp lambda p1 q1) := by
  refine ⟨one,one,lambda,⟨by decide,by decide⟩,
    ⟨by decide,by decide⟩,hl,?_⟩
  constructor <;>
    simp only [filledPatch,lerp,complement,one,Fraction.ofInt,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,
      Int.sub_mul,Int.mul_sub,Int.zero_mul,Int.mul_zero,Int.one_mul,
      Int.mul_one,Int.zero_add,Int.add_zero] <;>
    ac_nf <;> omega

end NewtonLimitDynamics.Polygon.FilledStrips
