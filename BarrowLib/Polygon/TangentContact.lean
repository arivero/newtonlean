import BarrowLib.Polygon.RationalBoundary
import BarrowLib.Common.UltimateScaling

/-!
Rational tangent contact on a concave, increasing graph patch.

Source of the precise coordinate statements and their derivations: the original
English statements and Lean proofs in this file. This records a project
reconstruction, not historical textual support, discovery or priority. The
mathematics uses finite rational arithmetic and ordered exhaustion only.

The tangent is specified by convergence of the slopes of chords issuing to
both sides. Concavity is specified independently by monotonicity of these
secant slopes. Neither supporting-line inequalities, tangent meetings nor
boundary approximation are premises. They are derived below. Existence of
such contact slopes for an arbitrary curve is not asserted. Vertical tangents
require a different coordinate patch.

Consumer: printed Lemma III Corollaries III-IV, NATP00077.par9-10 and
NATP00082.par10-11. The precise contact/concavity premises here are an editorial
coordinate reconstruction, not a quotation or new dependency attributed to
Newton. The area and arclength claims are separate from the boundary claim.
-/
namespace NewtonLimitDynamics.Polygon.TangentContact
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability
open SupportingTangents ConvexCover

def graph (g : Fraction → Fraction) (x : Fraction) : Point := (x, g x)

def rightSlope (g : Fraction → Fraction) (x h : Fraction) : Fraction :=
  if hh : Fraction.positive h then
    Fraction.quotient (durationDifference (g x) (g (Fraction.add x h))) h hh
  else Fraction.ofInt 0

def leftSlope (g : Fraction → Fraction) (x h : Fraction) : Fraction :=
  if hh : Fraction.positive h then
    Fraction.quotient (durationDifference (g (durationDifference h x)) (g x)) h hh
  else Fraction.ofInt 0

def line (g d : Fraction → Fraction) (x y : Fraction) : Fraction :=
  Fraction.add (g x) (Fraction.mul (d x) (durationDifference x y))

/-- Contact and secant concavity on the given patch, independent of the
desired support inequalities. One-sided contact is used at the endpoints.
Respect for equivalent rational representatives is an explicit premise. -/
structure Patch (g d : Fraction → Fraction) (a b : Fraction) : Prop where
  congr : ∀ x y, Fraction.equiv x y → Fraction.equiv (g x) (g y)
  slope_congr : ∀ x y, Fraction.equiv x y → Fraction.equiv (d x) (d y)
  right_concave : ∀ x h k, Fraction.le a x →
    Fraction.le (Fraction.add x k) b → Fraction.positive h → Fraction.positive k →
    Fraction.le h k → Fraction.le (rightSlope g x k) (rightSlope g x h)
  left_concave : ∀ x h k, Fraction.le x b →
    Fraction.le a (durationDifference k x) → Fraction.positive h → Fraction.positive k →
    Fraction.le h k → Fraction.le (leftSlope g x h) (leftSlope g x k)
  right_contact : ∀ x, Fraction.le a x → Fraction.lt x b →
    Ultimate Fraction.magnitudes (rightSlope g x) (d x)
  left_contact : ∀ x, Fraction.lt a x → Fraction.le x b →
    Ultimate Fraction.magnitudes (leftSlope g x) (d x)
  increasing_tangents : ∀ x, Fraction.le a x → Fraction.le x b → 0 ≤ (d x).num

/-- An eventual lower comparison survives ordered exhaustion. The proof
uses an actual positive sample in a common window, not a terminal-value axiom. -/
theorem ultimate_lower {r : Fraction → Fraction} {c v : Fraction}
    (hr : Ultimate Fraction.magnitudes r c)
    (hv : Near Fraction.magnitudes (fun h => Fraction.le v (r h))) : Fraction.le v c := by
  by_cases h : Fraction.le v c
  · exact h
  · have hcv : Fraction.lt c v := by unfold Fraction.le Fraction.lt at *; omega
    obtain ⟨l, _, hl, _⟩ := Fraction.magnitudes.surrounds c
    obtain ⟨t, _, ht, hv'⟩ := near_has_witness Fraction.magnitudes _
      (near_and Fraction.magnitudes _ _ (hr l v hl hcv) hv)
    exact False.elim (Fraction.magnitudes.lt_irrefl v
      (Fraction.magnitudes.lt_of_le_lt hv' ht.2))

theorem ultimate_upper {r : Fraction → Fraction} {c v : Fraction}
    (hr : Ultimate Fraction.magnitudes r c)
    (hv : Near Fraction.magnitudes (fun h => Fraction.le (r h) v)) : Fraction.le c v := by
  by_cases h : Fraction.le c v
  · exact h
  · have hvc : Fraction.lt v c := by unfold Fraction.le Fraction.lt at *; omega
    obtain ⟨_, u, _, hu⟩ := Fraction.magnitudes.surrounds c
    obtain ⟨t, _, ht, hv'⟩ := near_has_witness Fraction.magnitudes _
      (near_and Fraction.magnitudes _ _ (hr v u hvc hu) hv)
    exact False.elim (Fraction.magnitudes.lt_irrefl v
      (Fraction.magnitudes.lt_of_lt_le ht.1 hv'))

theorem difference_positive (x y : Fraction) (h : Fraction.lt x y) :
    Fraction.positive (durationDifference x y) := by
  unfold durationDifference negF Fraction.add Fraction.positive
  dsimp
  simp only [Int.neg_mul]
  unfold Fraction.lt at h
  omega

theorem add_difference (x y : Fraction) :
    Fraction.equiv (Fraction.add x (durationDifference x y)) y :=
  add_difference_cancel x y

theorem subtract_difference (x y : Fraction) :
    Fraction.equiv (durationDifference (durationDifference x y) y) x := by
  simp only [durationDifference, negF, Fraction.equiv, Fraction.add,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg]
  ac_nf
  omega

/-- Every finite right chord has slope at most the contact slope. -/
theorem right_below {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.lt x y) (hyb : Fraction.le y b) :
    Fraction.le (rightSlope g x (durationDifference x y)) (d x) := by
  let k := durationDifference x y
  have hk := difference_positive x y hxy
  apply ultimate_lower (C.right_contact x hax (Fraction.magnitudes.lt_of_lt_le hxy hyb))
  refine ⟨k, hk, fun h hh hhk => ?_⟩
  exact C.right_concave x h k hax (Fraction.le_equiv_left (add_difference x y) hyb)
    hh hk (Fraction.magnitudes.lt_implies_le hhk)

/-- Every finite left chord has slope at least the contact slope. -/
theorem left_above {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.lt x y) (hyb : Fraction.le y b) :
    Fraction.le (d y) (leftSlope g y (durationDifference x y)) := by
  let k := durationDifference x y
  have hk := difference_positive x y hxy
  apply ultimate_upper (C.left_contact y (Fraction.magnitudes.lt_of_le_lt hax hxy) hyb)
  refine ⟨k, hk, fun h hh hhk => ?_⟩
  exact C.left_concave y h k hyb
    (Fraction.le_equiv_right hax (Fraction.equiv_symm (subtract_difference x y)))
    hh hk (Fraction.magnitudes.lt_implies_le hhk)

theorem right_reconstruct (g : Fraction → Fraction) (x h : Fraction) (hh : Fraction.positive h) :
    Fraction.equiv (Fraction.mul (rightSlope g x h) h)
      (durationDifference (g x) (g (Fraction.add x h))) := by
  simp only [rightSlope, dite_eq_left hh, Fraction.quotient, Fraction.mul, Fraction.equiv]
  ac_rfl

theorem left_reconstruct (g : Fraction → Fraction) (x h : Fraction) (hh : Fraction.positive h) :
    Fraction.equiv (Fraction.mul (leftSlope g x h) h)
      (durationDifference (g (durationDifference h x)) (g x)) := by
  simp only [leftSlope, dite_eq_left hh, Fraction.quotient, Fraction.mul, Fraction.equiv]
  ac_rfl

theorem line_self (g d : Fraction → Fraction) (x : Fraction) :
    Fraction.equiv (line g d x x) (g x) := by
  simp only [line, durationDifference, negF, Fraction.equiv, Fraction.add, Fraction.mul,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

theorem line_target_congr (g d : Fraction → Fraction) (x : Fraction)
    {y z : Fraction} (hyz : Fraction.equiv y z) :
    Fraction.equiv (line g d x y) (line g d x z) :=
  Fraction.add_equiv_left _ (Fraction.mul_equiv_left _
    (difference_congr (Fraction.equiv_refl x) hyz))

/-- The left endpoint's tangent lies above the other endpoint of the arc.
This support inequality is derived from contact and concavity. -/
theorem support_from_left {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) :
    Fraction.le (g y) (line g d x y) := by
  by_cases he : Fraction.equiv x y
  · exact Fraction.le_of_equiv (Fraction.equiv_trans (Fraction.equiv_symm (C.congr x y he))
      (Fraction.equiv_symm (Fraction.equiv_trans
        (line_target_congr g d x (Fraction.equiv_symm he)) (line_self g d x))))
  · have hs : Fraction.lt x y := by unfold Fraction.equiv Fraction.le Fraction.lt at *; omega
    let k := durationDifference x y
    have hmul := Fraction.mul_le_mul_positive (right_below C x y hax hs hyb) k
      (difference_positive x y hs)
    have hv : Fraction.equiv (Fraction.add (g x) (Fraction.mul (rightSlope g x k) k)) (g y) :=
      Fraction.equiv_trans (Fraction.add_equiv_left _ (right_reconstruct g x k
        (difference_positive x y hs)))
        (Fraction.equiv_trans (add_difference (g x) (g (Fraction.add x k)))
          (C.congr _ _ (add_difference x y)))
    exact Fraction.le_equiv_left (Fraction.equiv_symm hv)
      (Fraction.add_le_add_left hmul (g x))

/-- The right endpoint's tangent likewise lies above the left endpoint. -/
theorem support_from_right {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) :
    Fraction.le (g x) (line g d y x) := by
  by_cases he : Fraction.equiv x y
  · exact Fraction.le_of_equiv (Fraction.equiv_trans (C.congr x y he)
      (Fraction.equiv_symm (Fraction.equiv_trans
        (line_target_congr g d y he) (line_self g d y))))
  · have hs : Fraction.lt x y := by unfold Fraction.equiv Fraction.le Fraction.lt at *; omega
    let k := durationDifference x y
    let v := Fraction.mul (d y) k
    have hmul := Fraction.mul_le_mul_positive (left_above C x y hax hs hyb) k
      (difference_positive x y hs)
    have hv : Fraction.equiv (Fraction.add (g x) (Fraction.mul (leftSlope g y k) k)) (g y) := by
      have hg := C.congr _ _ (subtract_difference x y)
      exact Fraction.equiv_trans (Fraction.add_equiv_left _
        (Fraction.equiv_trans (left_reconstruct g y k (difference_positive x y hs))
          (difference_congr hg (Fraction.equiv_refl _)))) (add_difference (g x) (g y))
    have hbound := Fraction.le_equiv_right (Fraction.add_le_add_left hmul (g x)) hv
    have hid : Fraction.equiv (Fraction.add v (line g d y x)) (g y) := by
      simp only [v, k, line, durationDifference, negF, Fraction.equiv, Fraction.add, Fraction.mul,
        Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
      ac_nf
      omega
    exact Fraction.le_add_cancel_left v _ _
      (Fraction.le_equiv_left (Fraction.add_comm v (g x))
        (Fraction.le_equiv_right hbound (Fraction.equiv_symm hid)))

private theorem line_increasing (g d : Fraction → Fraction) (x y : Fraction)
    (hxy : Fraction.le x y) (hd : 0 ≤ (d x).num) : Fraction.le (g x) (line g d x y) :=
  Fraction.le_add_nonnegative _ _ (Fraction.nonnegative_mul _ _ hd
    ((difference_nonnegative_iff x y).mpr hxy))

private theorem line_before (g d : Fraction → Fraction) (x y : Fraction)
    (hxy : Fraction.le x y) (hd : 0 ≤ (d y).num) : Fraction.le (line g d y x) (g y) := by
  have hn : (durationDifference y x).num ≤ 0 := by
    unfold durationDifference negF Fraction.add
    dsimp
    simp only [Int.neg_mul]
    unfold Fraction.le at hxy
    omega
  have hp : (Fraction.mul (d y) (durationDifference y x)).num ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hd hn
  unfold line Fraction.le Fraction.add
  dsimp
  simp only [Int.add_mul]
  have hm := Int.mul_nonpos_of_nonpos_of_nonneg hp
    (Int.le_of_lt (g y).den_pos)
  have hm' := Int.mul_nonpos_of_nonpos_of_nonneg hm
    (Int.le_of_lt (g y).den_pos)
  have he : (g y).num * (Fraction.mul (d y) (durationDifference y x)).den * (g y).den =
      (g y).num * ((g y).den * (Fraction.mul (d y) (durationDifference y x)).den) := by ac_rfl
  rw [he]
  omega

/-- The finite supporting cell is constructed from the two contact tangents.
No meeting or rectangle enclosure is among the patch premises. -/
def cell {g d : Fraction → Fraction} {a b : Fraction} (C : Patch g d a b)
    (x y : Fraction) (hax : Fraction.le a x) (hxy : Fraction.le x y) (hyb : Fraction.le y b) :
    Cell (graph g x) (graph g y) where
  leftEnd := (y, line g d x y)
  rightStart := (x, line g d y x)
  left_x := Fraction.equiv_refl _
  right_x := Fraction.equiv_refl _
  support := Or.inl ⟨support_from_right C x y hax hxy hyb, support_from_left C x y hax hxy hyb⟩
  monotone := Or.inl ⟨line_increasing g d x y hxy
    (C.increasing_tangents x hax (Fraction.magnitudes.le_trans hxy hyb)),
    line_before g d x y hxy (C.increasing_tangents y (Fraction.magnitudes.le_trans hax hxy) hyb)⟩

theorem monotone {g d : Fraction → Fraction} {a b : Fraction} (C : Patch g d a b) :
    MonotoneRectangles.MonotoneOn g a b := by
  intro x y hax hxy hyb
  exact Fraction.magnitudes.le_trans (support_from_right C x y hax hxy hyb)
    (line_before g d x y hxy
      (C.increasing_tangents y (Fraction.magnitudes.le_trans hax hxy) hyb))

theorem chord_slopes_equal {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hxy : Fraction.lt x y) :
    Fraction.equiv (rightSlope g x (durationDifference x y))
      (leftSlope g y (durationDifference x y)) := by
  let k := durationDifference x y
  have hk := difference_positive x y hxy
  have he : Fraction.equiv (Fraction.mul (rightSlope g x k) k)
      (Fraction.mul (leftSlope g y k) k) :=
    Fraction.equiv_trans (right_reconstruct g x k hk)
      (Fraction.equiv_trans
        (difference_congr (Fraction.equiv_refl _) (C.congr _ _ (add_difference x y)))
        (Fraction.equiv_trans
          (Fraction.equiv_symm (difference_congr (C.congr _ _ (subtract_difference x y))
            (Fraction.equiv_refl _)))
          (Fraction.equiv_symm (left_reconstruct g y k hk))))
  exact Fraction.mul_equiv_cancel_left k (Int.ne_of_gt hk)
    (Fraction.equiv_trans (Fraction.mul_comm _ _)
      (Fraction.equiv_trans he (Fraction.mul_comm _ _)))

/-- Contact slopes decrease on a concave patch; the left endpoint therefore
supplies a finite bound without a separately postulated continuity modulus. -/
theorem slopes_decrease {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) : Fraction.le (d y) (d x) := by
  by_cases he : Fraction.equiv x y
  · exact Fraction.le_of_equiv (Fraction.equiv_symm (C.slope_congr x y he))
  · have hs : Fraction.lt x y := by unfold Fraction.le Fraction.equiv Fraction.lt at *; omega
    exact Fraction.magnitudes.le_trans
      (Fraction.le_equiv_right (left_above C x y hax hs hyb)
        (Fraction.equiv_symm (chord_slopes_equal C x y hs)))
      (right_below C x y hax hs hyb)

theorem graph_distance {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) :
    Fraction.equiv (FiniteEstimates.pointDistance (graph g y) (graph g x))
      (Fraction.add (durationDifference x y) (durationDifference (g x) (g y))) :=
  Fraction.add_equiv
    (Fraction.abs_of_nonnegative _ ((difference_nonnegative_iff x y).mpr hxy))
    (Fraction.abs_of_nonnegative _ ((difference_nonnegative_iff _ _).mpr
      (monotone C x y hax hxy hyb)))

theorem graph_distance_bound {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) :
    Fraction.le (FiniteEstimates.pointDistance (graph g y) (graph g x))
      (Fraction.mul (durationDifference x y) (Fraction.add (Fraction.ofInt 1) (d a))) := by
  let k := durationDifference x y
  have hs := support_from_left C x y hax hxy hyb
  have hdiff : Fraction.le (durationDifference (g x) (g y)) (Fraction.mul (d x) k) :=
    Fraction.le_add_cancel_left (g x) _ _
      (Fraction.le_equiv_left (add_difference (g x) (g y)) hs)
  have hd := Fraction.mul_le_mul_nonnegative (slopes_decrease C a x
    (Fraction.magnitudes.le_refl _) hax (Fraction.magnitudes.le_trans hxy hyb))
    k ((difference_nonnegative_iff x y).mpr hxy)
  have hsum := Fraction.add_le_add_left (Fraction.magnitudes.le_trans hdiff hd) k
  exact Fraction.le_equiv_left (graph_distance C x y hax hxy hyb)
    (Fraction.le_equiv_right hsum (by
      simp only [k, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
        Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
      ac_nf))

/-- Uniform boundary continuity follows from the finite tangent bound and
the independent contact/concavity hypotheses. It is not supplied as a field. -/
theorem graph_uniform {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (hab : Fraction.le a b) : RationalBoundary.UniformOn (graph g) a b := by
  let K := Fraction.add (Fraction.ofInt 1) (d a)
  have hK : 0 ≤ K.num := Fraction.nonnegative_add _ _ (by decide)
    (C.increasing_tangents a (Fraction.magnitudes.le_refl _) hab)
  intro eps heps
  refine ⟨HarmonicTimeRealization.factorDelta K eps.half hK,
    HarmonicTimeRealization.factorDelta_positive K eps.half hK heps, ?_⟩
  intro x y hax hxb hay hyb hdist
  have hcontrol : Fraction.lt
      (Fraction.mul (durationDifference x y).abs K) eps := by
    -- Use a strict margin in the radius rather than turn a weak input into
    -- a strict output at the boundary of the chosen neighborhood.
    exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.magnitudes.le_trans (Fraction.mul_le_mul_nonnegative hdist K hK)
        (HarmonicTimeRealization.factor_delta_weak K eps.half hK (Int.le_of_lt heps)))
      (Fraction.half_lt eps heps)
  by_cases hxy : Fraction.le x y
  · exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_equiv_left (FiniteEstimates.pointDistance_symm _ _)
        (Fraction.le_equiv_right (graph_distance_bound C x y hax hxy hyb)
          (Fraction.mul_equiv_right K (Fraction.equiv_symm
            (Fraction.abs_of_nonnegative _ ((difference_nonnegative_iff x y).mpr hxy)))))) hcontrol
  · have hyx : Fraction.le y x := by unfold Fraction.le at *; omega
    have he := HarmonicTimeRealization.durationDifference_abs_symm y x
    exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_equiv_right (graph_distance_bound C y x hay hyx hxb)
        (Fraction.equiv_trans (Fraction.mul_equiv_right K (Fraction.equiv_symm
          (Fraction.abs_of_nonnegative _ ((difference_nonnegative_iff y x).mpr hyx))))
          (Fraction.mul_equiv_right K he))) hcontrol

def OnTangent (g d : Fraction → Fraction) (t : Fraction) (p : Point) : Prop :=
  Fraction.equiv p.2 (line g d t p.1)

private theorem line_affine (g d : Fraction → Fraction) (t u x y : Fraction) :
    Fraction.equiv (line g d t (affine u x y))
      (affine u (line g d t x) (line g d t y)) := by
  simp only [line, affine, complement, durationDifference, negF, Fraction.equiv,
    Fraction.add, Fraction.mul, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub,
    Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

theorem segment_on_tangent (g d : Fraction → Fraction) (t : Fraction) (p q x : Point)
    (hp : OnTangent g d t p) (hq : OnTangent g d t q)
    (hx : RationalBoundary.Segment p q x) : OnTangent g d t x := by
  obtain ⟨u, _, he⟩ := hx
  exact Fraction.equiv_trans he.2
    (Fraction.equiv_trans (Fraction.add_equiv (Fraction.mul_equiv_left _ hp)
      (Fraction.mul_equiv_left _ hq))
      (Fraction.equiv_symm (Fraction.equiv_trans (line_target_congr g d t he.1)
        (line_affine g d t u p.1 q.1))))

/-- The constructed meeting is on both of the actual contact lines. -/
theorem meeting_on_tangents {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) (r : Point)
    (hr : Meeting (graph g x) (graph g y) (cell C x y hax hxy hyb) r) :
    OnTangent g d x r ∧ OnTangent g d y r := by
  obtain ⟨u, hu, hl, hr⟩ := hr
  exact ⟨segment_on_tangent g d x (graph g x) (y, line g d x y) r (Fraction.equiv_symm (line_self g d x))
      (Fraction.equiv_refl _) ⟨u, hu, hl⟩,
    segment_on_tangent g d y (x, line g d y x) (graph g y) r (Fraction.equiv_refl _)
      (Fraction.equiv_symm (line_self g d y)) ⟨u, hu, hr⟩⟩

private def chordCell (p q : Point) : Cell p q := by
  refine ⟨q, p, Fraction.equiv_refl _, Fraction.equiv_refl _,
    Or.inl ⟨Fraction.magnitudes.le_refl _, Fraction.magnitudes.le_refl _⟩, ?_⟩
  by_cases h : Fraction.le p.2 q.2
  · exact Or.inl ⟨h,h⟩
  · have hr : Fraction.le q.2 p.2 := by unfold Fraction.le at *; omega
    exact Or.inr ⟨hr,hr⟩

/-- Only active cells of the partition are used. The total function's unused
indices receive a chord cell; no order or contact outside the patch is needed.
Repeated nodes remain active and are handled by the zero-width proofs. -/
def partitionCells {g d : Fraction → Fraction} {a b : Fraction} (C : Patch g d a b)
    (p : MonotoneRectangles.Partition a b) (i : Nat) :
    Cell (graph g (p.nodes i)) (graph g (p.nodes (i+1))) :=
  if hi : i < p.count then
    cell C _ _ (MonotoneRectangles.node_bounds p i (by omega)).1
      (p.ordered i hi) (MonotoneRectangles.node_bounds p (i+1) (by omega)).2
  else chordCell _ _

def Trace {g d : Fraction → Fraction} {a b : Fraction} (C : Patch g d a b)
    (p : MonotoneRectangles.Partition a b) : Point → Prop :=
  RationalBoundary.SupportingTrace (graph g) p (partitionCells C p)

/-- Every point of the finite joined trace lies on an endpoint contact
tangent. Infinite-line extensions are excluded by the segment predicates. -/
theorem trace_on_tangents {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) (z : Point) (hz : Trace C p z) :
    ∃ i, i < p.count ∧ (OnTangent g d (p.nodes i) z ∨ OnTangent g d (p.nodes (i+1)) z) := by
  obtain ⟨i, hi, r, hr, hz⟩ := hz
  have hr' := hr
  simp only [partitionCells, dite_eq_left hi] at hr'
  have ht := meeting_on_tangents C (p.nodes i) (p.nodes (i+1))
    (MonotoneRectangles.node_bounds p i (by omega)).1 (p.ordered i hi)
    (MonotoneRectangles.node_bounds p (i+1) (by omega)).2 r hr'
  refine ⟨i, hi, ?_⟩
  rcases hz with hz | hz
  · exact Or.inl (segment_on_tangent g d (p.nodes i) (graph g (p.nodes i)) r z
      (Fraction.equiv_symm (line_self g d _)) ht.1 hz)
  · exact Or.inr (segment_on_tangent g d (p.nodes (i+1)) r (graph g (p.nodes (i+1))) z ht.2
      (Fraction.equiv_symm (line_self g d _)) hz)

/-- The actual rational polygonal region under the two endpoint tangents in
each cell: its upper height is the lesser of the two affine heights. -/
def figure (g d : Fraction → Fraction) {a b : Fraction}
    (p : MonotoneRectangles.Partition a b) (z : Point) : Prop :=
  ∃ i, i < p.count ∧ Fraction.le (p.nodes i) z.1 ∧ Fraction.le z.1 (p.nodes (i+1)) ∧
    0 ≤ z.2.num ∧ Fraction.le z.2 (line g d (p.nodes i) z.1) ∧
    Fraction.le z.2 (line g d (p.nodes (i+1)) z.1)

/-- The tangent polygon circumscribes the curved figure and stays inside
its endpoint rectangle cover. Both inclusions follow from contact/concavity. -/
theorem figure_enclosure {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) :
    (∀ z, MonotoneRectangles.figure g a b z → figure g d p z) ∧
    (∀ z, figure g d p z → MonotoneRectangles.upperFigure g p z) := by
  constructor
  · intro z hz
    obtain ⟨ha, hb, hy, hg⟩ := hz
    obtain ⟨i, hi, hl, hr⟩ := MonotoneRectangles.partition_cover p z.1 ha hb
    exact ⟨i, hi, hl, hr, hy,
      Fraction.magnitudes.le_trans hg (support_from_left C _ _
        (MonotoneRectangles.node_bounds p i (by omega)).1 hl hb),
      Fraction.magnitudes.le_trans hg (support_from_right C _ _ ha hr
        (MonotoneRectangles.node_bounds p (i+1) (by omega)).2)⟩
  · rintro z ⟨i, hi, hl, hr, hy, _, hu⟩
    exact ⟨i, hi, hl, hr, hy, Fraction.magnitudes.le_trans hu
      (line_before g d _ _ hr (C.increasing_tangents _
        (MonotoneRectangles.node_bounds p (i+1) (by omega)).1
        (MonotoneRectangles.node_bounds p (i+1) (by omega)).2))⟩

end NewtonLimitDynamics.Polygon.TangentContact
