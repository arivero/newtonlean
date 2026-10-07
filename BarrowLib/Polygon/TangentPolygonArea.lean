import BarrowLib.Polygon.TangentBoundary
import BarrowLib.Polygon.TriangleContent

/-!
Area of the actual finite contact-tangent polygon.

Source of these precise coordinate statements and derivations: the original
English statements and Lean proofs in this file. They identify a project
reconstruction, without historical textual-support, discovery or priority
claims. The consumer is Lemma III Corollary III, NATP00077.par9 and
NATP00082.par10; the historical result file retains each exact Latin statement.

The area convention supplies elementary rectangle/triangle normalization,
cut additivity and translation invariance, not the tangent polygon's area.
Each actual cell is dissected at a constructed contact-tangent meeting, its
two affine subgraph areas are derived, and vertical partition cuts add them.
Coincident lines, zero slopes and repeated nodes require no exclusion. The
curved region's area and exhaustion of the chosen mesh remain separate.
-/
namespace NewtonLimitDynamics.Polygon.TangentPolygonArea
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability
open SupportingTangents TangentContact TriangleContent PolygonFanArea

def trapezoid (p q : Point) : Fraction :=
  Fraction.mul (durationDifference p.1 q.1) (Fraction.add p.2 q.2).half

theorem trapezoid_congr {p p' q q' : Point} (hp : pointEquiv p p') (hq : pointEquiv q q') :
    Fraction.equiv (trapezoid p q) (trapezoid p' q') :=
  Fraction.mul_equiv (difference_congr hp.1 hq.1)
    (RationalIntervals.half_equiv (Fraction.add_equiv hp.2 hq.2))

def LineRegion (g d : Fraction → Fraction) (t l r : Fraction) (z : Point) : Prop :=
  Fraction.le l z.1 ∧ Fraction.le z.1 r ∧ 0 ≤ z.2.num ∧ Fraction.le z.2 (line g d t z.1)

theorem line_reanchor (g d : Fraction → Fraction) (t l x : Fraction) :
    Fraction.equiv (line g d t x) (height l (line g d t l) (d t) x) := by
  simp only [line, height, durationDifference, negF, Fraction.equiv, Fraction.add, Fraction.mul,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

theorem line_region_area (area : TriangleContent.AreaRules) (g d : Fraction → Fraction)
    (t l r : Fraction) (hlr : Fraction.le l r)
    (hH : 0 ≤ (line g d t l).num) (hs : 0 ≤ (d t).num) :
    area.HasArea (LineRegion g d t l r)
      (trapezoid (l,line g d t l) (r,line g d t r)) := by
  have hu := underLine_area area l r (line g d t l) (d t) hlr hH hs
  have hv := area.congr_value _ _ _ (Fraction.mul_equiv_left (durationDifference l r)
    (RationalIntervals.half_equiv (Fraction.add_equiv_left _
      (Fraction.equiv_symm (line_reanchor g d t l r))))) hu
  apply area.congr_set _ _ _ _ hv
  intro z
  constructor
  · rintro ⟨hl,hr,hy,hheight⟩
    exact ⟨hl,hr,hy,Fraction.le_equiv_right hheight (Fraction.equiv_symm (line_reanchor g d t l z.1))⟩
  · rintro ⟨hl,hr,hy,hheight⟩
    exact ⟨hl,hr,hy,Fraction.le_equiv_right hheight (line_reanchor g d t l z.1)⟩

def CellRegion (g d : Fraction → Fraction) (x y : Fraction) (z : Point) : Prop :=
  Fraction.le x z.1 ∧ Fraction.le z.1 y ∧ 0 ≤ z.2.num ∧
  Fraction.le z.2 (line g d x z.1) ∧ Fraction.le z.2 (line g d y z.1)

/-- The actual lesser-tangent cell is the union of two affine subgraphs at
any constructed meeting. The lower-envelope order is proved by interpolation. -/
theorem cell_dissection {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) (r : Point)
    (hr : Meeting (graph g x) (graph g y) (cell C x y hax hxy hyb) r) (z : Point) :
    CellRegion g d x y z ↔ LineRegion g d x x r.1 z ∨ LineRegion g d y r.1 y z := by
  have hb := (meeting_bounds C x y hax hxy hyb r hr).1
  constructor
  · rintro ⟨hl,hu,hy,hL,hR⟩
    by_cases hzr : Fraction.le z.1 r.1
    · exact Or.inl ⟨hl,hzr,hy,hL⟩
    · have hrz : Fraction.le r.1 z.1 := by unfold Fraction.le at *; omega
      exact Or.inr ⟨hrz,hu,hy,hR⟩
  · intro hz
    rcases hz with hz | hz
    · have hzy := Fraction.magnitudes.le_trans hz.2.1 hb.2
      have hLR := (lines_order_at_meeting C x y hax hxy hyb r hr z.1 hz.1 hzy).1 hz.2.1
      exact ⟨hz.1,hzy,hz.2.2.1,hz.2.2.2,Fraction.magnitudes.le_trans hz.2.2.2 hLR⟩
    · have hxz := Fraction.magnitudes.le_trans hb.1 hz.1
      have hRL := (lines_order_at_meeting C x y hax hxy hyb r hr z.1 hxz hz.2.1).2 hz.1
      exact ⟨hxz,hz.2.1,hz.2.2.1,Fraction.magnitudes.le_trans hz.2.2.2 hRL,hz.2.2.2⟩

/-- Area of the actual tangent cell, derived from two trapezoids. The
meeting and support are geometric constructions, not area premises. -/
theorem cell_area (area : TriangleContent.AreaRules)
    {g d : Fraction → Fraction} {a b : Fraction} (C : Patch g d a b)
    (x y : Fraction) (hax : Fraction.le a x) (hxy : Fraction.le x y)
    (hyb : Fraction.le y b) (hx : 0 ≤ (g x).num) (r : Point)
    (hr : Meeting (graph g x) (graph g y) (cell C x y hax hxy hyb) r) :
    area.HasArea (CellRegion g d x y)
      (Fraction.add (trapezoid (graph g x) r) (trapezoid r (graph g y))) := by
  have hb := meeting_bounds C x y hax hxy hyb r hr
  have ht := meeting_on_tangents C x y hax hxy hyb r hr
  have hL := line_region_area area g d x x r.1 hb.1.1
    (Fraction.nonnegative_equiv (line_self g d x) hx)
    (C.increasing_tangents x hax (Fraction.magnitudes.le_trans hxy hyb))
  have hR := line_region_area area g d y r.1 y hb.1.2
    (Fraction.nonnegative_equiv (Fraction.equiv_symm ht.2) (Fraction.nonnegative_of_le hx hb.2.1))
    (C.increasing_tangents y (Fraction.magnitudes.le_trans hax hxy) hyb)
  have hL' := area.congr_value _ _ _
    (trapezoid_congr (p:=(x,line g d x x)) (p':=graph g x)
      (q:=(r.1,line g d x r.1)) (q':=r) ⟨Fraction.equiv_refl _,line_self g d x⟩
      ⟨Fraction.equiv_refl _,Fraction.equiv_symm ht.1⟩) hL
  have hR' := area.congr_value _ _ _
    (trapezoid_congr (p:=(r.1,line g d y r.1)) (p':=r)
      (q:=(y,line g d y y)) (q':=graph g y) ⟨Fraction.equiv_refl _,Fraction.equiv_symm ht.2⟩
      ⟨Fraction.equiv_refl _,line_self g d y⟩) hR
  have hu := area.separated_union _ _ _ _ r.1 (fun _ hz => hz.2.1)
    (fun _ hz => hz.1) hL' hR'
  exact area.congr_set _ _ _ (fun z => (cell_dissection C x y hax hxy hyb r hr z).symm) hu

noncomputable def meeting {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) (i : Nat) : Point :=
  Classical.choose (meeting_exists (graph g (p.nodes i)) (graph g (p.nodes (i+1)))
    (partitionCells C p i))

theorem meeting_spec {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) (i : Nat) :
    Meeting (graph g (p.nodes i)) (graph g (p.nodes (i+1))) (partitionCells C p i) (meeting C p i) :=
  Classical.choose_spec (meeting_exists _ _ (partitionCells C p i))

noncomputable def cellValue {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) (i : Nat) : Fraction :=
  Fraction.add (trapezoid (graph g (p.nodes i)) (meeting C p i))
    (trapezoid (meeting C p i) (graph g (p.nodes (i+1))))

noncomputable def value {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) : Fraction :=
  sum (cellValue C p) p.count

def prefixRegion (g d : Fraction → Fraction) {a b : Fraction}
    (p : MonotoneRectangles.Partition a b) (n : Nat) (z : Point) : Prop :=
  ∃ i, i < n ∧ CellRegion g d (p.nodes i) (p.nodes (i+1)) z

private theorem prefix_succ (g d : Fraction → Fraction) {a b : Fraction}
    (p : MonotoneRectangles.Partition a b) (n : Nat) (z : Point) :
    prefixRegion g d p (n+1) z ↔ prefixRegion g d p n z ∨
      CellRegion g d (p.nodes n) (p.nodes (n+1)) z := by
  constructor
  · rintro ⟨i,hi,hz⟩
    by_cases hn : i < n
    · exact Or.inl ⟨i,hn,hz⟩
    · have he : i = n := by omega
      subst i
      exact Or.inr hz
  · intro h
    exact h.elim (fun ⟨i,hi,hz⟩ => ⟨i,by omega,hz⟩) (fun hz => ⟨n,by omega,hz⟩)

theorem prefix_area (area : TriangleContent.AreaRules)
    {g d : Fraction → Fraction} {a b : Fraction} (C : Patch g d a b)
    (p : MonotoneRectangles.Partition a b) (hbase : 0 ≤ (g a).num) (n : Nat) (hn : n ≤ p.count) :
    area.HasArea (prefixRegion g d p n) (sum (cellValue C p) n) := by
  induction n with
  | zero =>
    apply area.congr_set (fun _ => False) _ _ _ area.empty
    intro z
    simp only [prefixRegion, Nat.not_lt_zero, false_and, exists_false]
  | succ n ih =>
    have hi : n < p.count := by omega
    have hprev := ih (by omega)
    have hr := meeting_spec C p n
    simp only [partitionCells, dif_pos hi] at hr
    have hcell := cell_area area C (p.nodes n) (p.nodes (n+1))
      (MonotoneRectangles.node_bounds p n (by omega)).1 (p.ordered n hi)
      (MonotoneRectangles.node_bounds p (n+1) (by omega)).2
      (Fraction.nonnegative_of_le hbase (monotone C a (p.nodes n)
        (Fraction.magnitudes.le_refl _) (MonotoneRectangles.node_bounds p n (by omega)).1
        (MonotoneRectangles.node_bounds p n (by omega)).2)) (meeting C p n) hr
    have hu := area.separated_union _ _ _ _ (p.nodes n) ?_ ?_ hprev hcell
    · exact area.congr_set _ _ _ (fun z => (prefix_succ g d p n z).symm) hu
    · rintro z ⟨i,hi,hz⟩
      exact Fraction.magnitudes.le_trans hz.2.1
        (MonotoneRectangles.node_order p n (i+1) (by omega) (by omega))
    · intro z hz
      exact hz.1

/-- The actual finite circumscribed polygon has the displayed sum of
trapezoid areas. Only the elementary geometric area convention and contact
patch are supplied; its polygon-area assignment is a conclusion. -/
theorem polygon_area (area : TriangleContent.AreaRules)
    {g d : Fraction → Fraction} {a b : Fraction} (C : Patch g d a b)
    (p : MonotoneRectangles.Partition a b) (hbase : 0 ≤ (g a).num) :
    area.HasArea (TangentContact.figure g d p) (value C p) :=
  prefix_area area C p hbase p.count (Nat.le_refl _)

end NewtonLimitDynamics.Polygon.TangentPolygonArea
