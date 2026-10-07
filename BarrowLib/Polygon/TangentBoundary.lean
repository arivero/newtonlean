import BarrowLib.Polygon.TangentContact
import BarrowLib.Polygon.RadialSector

/-!
The joined contact-tangent trace is the upper boundary of its polygonal region.

Source of these precise coordinate statements and derivations: the original
English statements and Lean proofs in this file. They are project coordinate
reconstructions, without a claim of historical textual support, discovery or
priority. The consumer is printed Lemma III Corollary III, NATP00077.par9 and
NATP00082.par10, whose exact Latin remains in the historical result file.

Only finite rational interpolation is needed. An upper boundary point is in
an active cell, below both endpoint contact lines and on at least one. The
joined segments from the endpoints to their constructed meeting give exactly
these points, including coincident lines and repeated nodes. With nonnegative
initial graph height this is the top of TangentContact.figure above its
baseline. No area existence, curve completion or arclength is asserted.
-/
namespace NewtonLimitDynamics.Polygon.TangentContact
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability
open SupportingTangents ConvexCover

private theorem between_ordered {a b t : Fraction} (hab : Fraction.le a b)
    (ht : Between a t b) : Fraction.le a t ∧ Fraction.le t b := by
  rcases ht with ht | ht
  · exact ht
  · exact ⟨Fraction.magnitudes.le_trans hab ht.1,
      Fraction.magnitudes.le_trans ht.2 hab⟩

private theorem segment_below_line (g d : Fraction → Fraction) (t : Fraction)
    (p q z : Point) (hp : Fraction.le p.2 (line g d t p.1))
    (hq : Fraction.le q.2 (line g d t q.1)) (hz : RationalBoundary.Segment p q z) :
    Fraction.le z.2 (line g d t z.1) := by
  obtain ⟨u, hu, he⟩ := hz
  have h := Fraction.add_le_add
    (Fraction.mul_le_mul_nonnegative_left hp (complement u) (complement_nonnegative u hu))
    (Fraction.mul_le_mul_nonnegative_left hq u hu.1)
  have hl : OnTangent g d t
      (lerp u (p.1, line g d t p.1) (q.1, line g d t q.1)) :=
    segment_on_tangent g d t (p.1, line g d t p.1) (q.1, line g d t q.1)
      (lerp u (p.1, line g d t p.1) (q.1, line g d t q.1))
      (Fraction.equiv_refl _) (Fraction.equiv_refl _)
      ⟨u, hu, Fraction.equiv_refl _, Fraction.equiv_refl _⟩
  exact Fraction.le_equiv_left he.2 (Fraction.le_equiv_right h
    (Fraction.equiv_trans hl (line_target_congr g d t (Fraction.equiv_symm he.1))))

private theorem tangent_segment_at (g d : Fraction → Fraction) (t : Fraction)
    (p q : Point) (hp : OnTangent g d t p) (hq : OnTangent g d t q)
    (x : Fraction) (hl : Fraction.le p.1 x) (hr : Fraction.le x q.1) :
    RationalBoundary.Segment p q (x, line g d t x) := by
  obtain ⟨u, hu, he⟩ := RadialSector.interval_parameter p.1 q.1 x hl hr
  have ht : OnTangent g d t (lerp u p q) :=
    segment_on_tangent g d t p q _ hp hq
      ⟨u, hu, Fraction.equiv_refl _, Fraction.equiv_refl _⟩
  exact ⟨u, hu, Fraction.equiv_symm he,
    Fraction.equiv_trans (line_target_congr g d t (Fraction.equiv_symm he))
      (Fraction.equiv_symm ht)⟩

/-- The lesser of two affine contact heights, described without choosing a
particular rational representative or a unique intersection. -/
def CellUpper (g d : Fraction → Fraction) (x y : Fraction) (z : Point) : Prop :=
  Fraction.le x z.1 ∧ Fraction.le z.1 y ∧
  Fraction.le z.2 (line g d x z.1) ∧ Fraction.le z.2 (line g d y z.1) ∧
  (OnTangent g d x z ∨ OnTangent g d y z)

private def Joined {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) (z : Point) : Prop :=
  ∃ r, Meeting (graph g x) (graph g y) (cell C x y hax hxy hyb) r ∧
    (RationalBoundary.Segment (graph g x) r z ∨ RationalBoundary.Segment r (graph g y) z)

private theorem joined_upper {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) (z : Point)
    (hz : Joined C x y hax hxy hyb z) : CellUpper g d x y z := by
  obtain ⟨r, hr, hz⟩ := hz
  have hb := between_ordered hxy
    (RationalBoundary.supporting_rectangle (graph g x) (graph g y)
      (cell C x y hax hxy hyb) r z hr hz).1
  have ht := meeting_on_tangents C x y hax hxy hyb r hr
  have hp : OnTangent g d x (graph g x) := Fraction.equiv_symm (line_self g d x)
  have hq : OnTangent g d y (graph g y) := Fraction.equiv_symm (line_self g d y)
  rcases hz with hz | hz
  · exact ⟨hb.1, hb.2,
      Fraction.le_of_equiv (segment_on_tangent g d x (graph g x) r z hp ht.1 hz),
      segment_below_line g d y (graph g x) r z (support_from_right C x y hax hxy hyb)
        (Fraction.le_of_equiv ht.2) hz,
      Or.inl (segment_on_tangent g d x (graph g x) r z hp ht.1 hz)⟩
  · exact ⟨hb.1, hb.2,
      segment_below_line g d x r (graph g y) z (Fraction.le_of_equiv ht.1)
        (support_from_left C x y hax hxy hyb) hz,
      Fraction.le_of_equiv (segment_on_tangent g d y r (graph g y) z ht.2 hq hz),
      Or.inr (segment_on_tangent g d y r (graph g y) z ht.2 hq hz)⟩

private theorem cell_top_at {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b)
    (t : Fraction) (hxt : Fraction.le x t) (hty : Fraction.le t y) :
    ∃ h, Joined C x y hax hxy hyb (t,h) ∧ CellUpper g d x y (t,h) := by
  obtain ⟨r, hr⟩ := meeting_exists (graph g x) (graph g y) (cell C x y hax hxy hyb)
  have ht := meeting_on_tangents C x y hax hxy hyb r hr
  by_cases htr : Fraction.le t r.1
  · have hz : Joined C x y hax hxy hyb (t, line g d x t) :=
      ⟨r, hr, Or.inl (tangent_segment_at g d x (graph g x) r
        (Fraction.equiv_symm (line_self g d x)) ht.1 t hxt htr)⟩
    exact ⟨_, hz, joined_upper C x y hax hxy hyb _ hz⟩
  · have hrt : Fraction.le r.1 t := by unfold Fraction.le at *; omega
    have hz : Joined C x y hax hxy hyb (t, line g d y t) :=
      ⟨r, hr, Or.inr (tangent_segment_at g d y r (graph g y) ht.2
        (Fraction.equiv_symm (line_self g d y)) t hrt hty)⟩
    exact ⟨_, hz, joined_upper C x y hax hxy hyb _ hz⟩

private theorem lesser_height_unique (l r u v : Fraction)
    (hu : Fraction.le u l ∧ Fraction.le u r ∧ (Fraction.equiv u l ∨ Fraction.equiv u r))
    (hv : Fraction.le v l ∧ Fraction.le v r ∧ (Fraction.equiv v l ∨ Fraction.equiv v r)) :
    Fraction.equiv u v := by
  apply (Fraction.equiv_iff_mutual_le u v).mpr
  constructor
  · rcases hv.2.2 with h | h
    · exact Fraction.le_equiv_right hu.1 (Fraction.equiv_symm h)
    · exact Fraction.le_equiv_right hu.2.1 (Fraction.equiv_symm h)
  · rcases hu.2.2 with h | h
    · exact Fraction.le_equiv_right hv.1 (Fraction.equiv_symm h)
    · exact Fraction.le_equiv_right hv.2.1 (Fraction.equiv_symm h)

private theorem upper_joined {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hxy : Fraction.le x y) (hyb : Fraction.le y b) (z : Point)
    (hz : CellUpper g d x y z) : Joined C x y hax hxy hyb z := by
  obtain ⟨h, ⟨r, hr, hs⟩, hu⟩ := cell_top_at C x y hax hxy hyb z.1 hz.1 hz.2.1
  have he : pointEquiv z (z.1,h) := ⟨Fraction.equiv_refl _, lesser_height_unique _ _ _ _
    ⟨hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2⟩ ⟨hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2⟩⟩
  have transfer (p q : Point) (hh : RationalBoundary.Segment p q (z.1,h)) :
      RationalBoundary.Segment p q z := by
    obtain ⟨u, hu, hh⟩ := hh
    exact ⟨u, hu, pointEquiv_trans he hh⟩
  exact ⟨r, hr, hs.elim (fun hs => Or.inl (transfer _ _ hs))
    (fun hs => Or.inr (transfer _ _ hs))⟩

/-- The upper boundary of the cellwise tangent polygon, before choosing a
baseline. Points are below both endpoint lines and on the lesser one. -/
def UpperBoundary (g d : Fraction → Fraction) {a b : Fraction}
    (p : MonotoneRectangles.Partition a b) (z : Point) : Prop :=
  ∃ i, i < p.count ∧ CellUpper g d (p.nodes i) (p.nodes (i+1)) z

private theorem cell_upper_above_graph {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x y : Fraction) (hax : Fraction.le a x)
    (hyb : Fraction.le y b) (z : Point) (hz : CellUpper g d x y z) :
    Fraction.le (g z.1) z.2 := by
  rcases hz.2.2.2.2 with ht | ht
  · exact Fraction.le_equiv_right
      (support_from_left C x z.1 hax hz.1
        (Fraction.magnitudes.le_trans hz.2.1 hyb)) (Fraction.equiv_symm ht)
  · exact Fraction.le_equiv_right
      (support_from_right C z.1 y (Fraction.magnitudes.le_trans hax hz.1) hz.2.1 hyb)
      (Fraction.equiv_symm ht)

private theorem line_at_node {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (x t : Fraction) (ht : Fraction.equiv t x) :
    Fraction.equiv (line g d x t) (g t) :=
  Fraction.equiv_trans (line_target_congr g d x ht)
    (Fraction.equiv_trans (line_self g d x) (C.congr x t (Fraction.equiv_symm ht)))

/-- An upper boundary point is above every filled-region point at the same
abscissa, including when those points use different cells. The proof uses
partition order: distinct cells can overlap only at shared endpoint values. -/
theorem upperBoundary_maximal {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) (z : Point)
    (h : Fraction) (hz : figure g d p z) (ht : UpperBoundary g d p (z.1,h)) :
    Fraction.le z.2 h := by
  obtain ⟨i, hi, hl, hr, _, hL, hR⟩ := hz
  obtain ⟨j, hj, hu⟩ := ht
  have hg : Fraction.le (g z.1) h := cell_upper_above_graph C _ _
    (MonotoneRectangles.node_bounds p j (by omega)).1
    (MonotoneRectangles.node_bounds p (j+1) (by omega)).2 (z.1,h) hu
  by_cases he : i = j
  · subst j
    rcases hu.2.2.2.2 with ht | ht
    · exact Fraction.le_equiv_right hL (Fraction.equiv_symm ht)
    · exact Fraction.le_equiv_right hR (Fraction.equiv_symm ht)
  · by_cases hij : i < j
    · have hc := MonotoneRectangles.node_order p j (i+1) (by omega) (by omega)
      have heq : Fraction.equiv z.1 (p.nodes (i+1)) :=
        (Fraction.equiv_iff_mutual_le _ _).mpr
          ⟨hr, Fraction.magnitudes.le_trans hc hu.1⟩
      exact Fraction.magnitudes.le_trans
        (Fraction.le_equiv_right hR (line_at_node C _ _ heq)) hg
    · have hc := MonotoneRectangles.node_order p i (j+1) (by omega) (by omega)
      have heq : Fraction.equiv z.1 (p.nodes i) :=
        (Fraction.equiv_iff_mutual_le _ _).mpr
          ⟨Fraction.magnitudes.le_trans hu.2.1 hc, hl⟩
      exact Fraction.magnitudes.le_trans
        (Fraction.le_equiv_right hL (line_at_node C _ _ heq)) hg

/-- Exact identification of the joined finite tangent trace with the
polygonal region's upper boundary. No area or limiting premise is needed. -/
theorem trace_iff_upperBoundary {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) (z : Point) :
    Trace C p z ↔ UpperBoundary g d p z := by
  constructor
  · rintro ⟨i, hi, r, hr, hz⟩
    simp only [partitionCells, dif_pos hi] at hr
    exact ⟨i, hi, joined_upper C _ _
      (MonotoneRectangles.node_bounds p i (by omega)).1 (p.ordered i hi)
      (MonotoneRectangles.node_bounds p (i+1) (by omega)).2 z ⟨r, hr, hz⟩⟩
  · rintro ⟨i, hi, hz⟩
    obtain ⟨r, hr, hs⟩ := upper_joined C _ _
      (MonotoneRectangles.node_bounds p i (by omega)).1 (p.ordered i hi)
      (MonotoneRectangles.node_bounds p (i+1) (by omega)).2 z hz
    refine ⟨i, hi, r, ?_, hs⟩
    simpa only [partitionCells, dif_pos hi] using hr

/-- The upper boundary belongs to the filled tangent polygon when the
patch starts on or above the baseline. -/
theorem upperBoundary_in_figure {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b)
    (hbase : 0 ≤ (g a).num) (z : Point) (hz : UpperBoundary g d p z) : figure g d p z := by
  obtain ⟨i, hi, hl, hr, hL, hR, ht⟩ := hz
  have ha := (MonotoneRectangles.node_bounds p i (by omega)).1
  have hb := (MonotoneRectangles.node_bounds p (i+1) (by omega)).2
  have hza := Fraction.magnitudes.le_trans ha hl
  have hzb := Fraction.magnitudes.le_trans hr hb
  have hg := Fraction.nonnegative_of_le hbase (monotone C a z.1
    (Fraction.magnitudes.le_refl _) hza hzb)
  have hgz := cell_upper_above_graph C _ _ ha hb z ⟨hl,hr,hL,hR,ht⟩
  exact ⟨i, hi, hl, hr, Fraction.nonnegative_of_le hg hgz, hL, hR⟩

/-- Every point of the filled tangent polygon is vertically below a point
of the joined tangent trace with exactly the same abscissa representative. -/
theorem figure_below_trace {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b) (z : Point)
    (hz : figure g d p z) : ∃ h, Trace C p (z.1,h) ∧ Fraction.le z.2 h := by
  obtain ⟨i, hi, hl, hr, _, hL, hR⟩ := hz
  obtain ⟨h, _, hu⟩ := cell_top_at C _ _
    (MonotoneRectangles.node_bounds p i (by omega)).1 (p.ordered i hi)
    (MonotoneRectangles.node_bounds p (i+1) (by omega)).2 z.1 hl hr
  refine ⟨h, (trace_iff_upperBoundary C p _).mpr ⟨i, hi, hu⟩, ?_⟩
  rcases hu.2.2.2.2 with ht | ht
  · exact Fraction.le_equiv_right hL (Fraction.equiv_symm ht)
  · exact Fraction.le_equiv_right hR (Fraction.equiv_symm ht)

/-- The vertical top of the actual filled region, defined using region
membership and maximal height, independently of tangents or trace segments. -/
def VerticalTop (g d : Fraction → Fraction) {a b : Fraction}
    (p : MonotoneRectangles.Partition a b) (z : Point) : Prop :=
  figure g d p z ∧ ∀ h, figure g d p (z.1,h) → Fraction.le h z.2

/-- The algebraic lesser-tangent boundary is exactly the vertical top of
the filled polygon. This is a finite rational set identity, not a claim about
topological boundaries in a completed plane. -/
theorem upperBoundary_iff_verticalTop {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b)
    (hbase : 0 ≤ (g a).num) (z : Point) :
    UpperBoundary g d p z ↔ VerticalTop g d p z := by
  constructor
  · intro hz
    refine ⟨upperBoundary_in_figure C p hbase z hz, ?_⟩
    intro h hh
    exact upperBoundary_maximal C p (z.1,h) z.2 hh hz
  · intro hz
    obtain ⟨h, ht, hzh⟩ := figure_below_trace C p z hz.1
    have hu := (trace_iff_upperBoundary C p (z.1,h)).mp ht
    have hh := hz.2 h (upperBoundary_in_figure C p hbase (z.1,h) hu)
    have he := (Fraction.equiv_iff_mutual_le z.2 h).mpr ⟨hzh,hh⟩
    obtain ⟨i, hi, hl, hr, hL, hR, hline⟩ := hu
    refine ⟨i, hi, hl, hr, Fraction.le_equiv_left he hL,
      Fraction.le_equiv_left he hR, ?_⟩
    exact hline.elim (fun ht => Or.inl (Fraction.equiv_trans he ht))
      (fun ht => Or.inr (Fraction.equiv_trans he ht))

/-- The joined finite contact tangents are precisely the vertical top of
the circumscribed polygon above the baseline. -/
theorem trace_iff_verticalTop {g d : Fraction → Fraction} {a b : Fraction}
    (C : Patch g d a b) (p : MonotoneRectangles.Partition a b)
    (hbase : 0 ≤ (g a).num) (z : Point) : Trace C p z ↔ VerticalTop g d p z :=
  (trace_iff_upperBoundary C p z).trans (upperBoundary_iff_verticalTop C p hbase z)

end NewtonLimitDynamics.Polygon.TangentContact
