import BarrowLib.Polygon.MonotoneRectangles
import BarrowLib.Polygon.SupportingTangents
import BarrowLib.Common.Exhaustion

/-! Two-sided approximation of a given rationally parameterized curve by
finite rectangle, chord and supporting-segment traces. These elementary
estimates construct no completion, derivative, tangent or arclength. Uniform
continuity and the supporting-line data, when used, are explicit premises.
Area exhaustion alone is not a premise sufficient for these boundary claims. -/
namespace NewtonLimitDynamics.Polygon.RationalBoundary
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles
open FiniteEstimates PointBounds ConvexCover SupportingTangents HarmonicTimeComparison

def CurveTrace (f : Fraction → Point) (a b : Fraction) (x : Point) : Prop :=
  ∃ t, Fraction.le a t ∧ Fraction.le t b ∧ pointEquiv x (f t)

def UniformOn (f : Fraction → Point) (a b : Fraction) : Prop :=
  ∀ eps : Fraction, 0 < eps.num → ∃ delta : Fraction, 0 < delta.num ∧
    ∀ s t, Fraction.le a s → Fraction.le s b → Fraction.le a t → Fraction.le t b →
      Fraction.le (durationDifference s t).abs delta → Fraction.lt (pointDistance (f s) (f t)) eps

def Approaches (traces : Nat → Point → Prop) (curve : Point → Prop) : Prop :=
  ∀ eps : Fraction, 0 < eps.num → ∃ N, ∀ m, N ≤ m →
    (∀ x, traces m x → ∃ y, curve y ∧ Fraction.lt (pointDistance x y) eps) ∧
    (∀ y, curve y → ∃ x, traces m x ∧ Fraction.lt (pointDistance y x) eps)

def RectangleTrace (f : Fraction → Point) {a b : Fraction} (p : Partition a b) (x : Point) : Prop :=
  ∃ i, i < p.count ∧ RectangleBetween (f (p.nodes i)) x (f (p.nodes (i+1)))

def Segment (p q x : Point) : Prop :=
  ∃ u, UnitInterval u ∧ pointEquiv x (lerp u p q)

def ChordTrace (f : Fraction → Point) {a b : Fraction} (p : Partition a b) (x : Point) : Prop :=
  ∃ i, i < p.count ∧ Segment (f (p.nodes i)) (f (p.nodes (i+1))) x

def NodeTrace (f : Fraction → Point) {a b : Fraction} (p : Partition a b) (x : Point) : Prop :=
  ∃ i, i < p.count ∧ pointEquiv x (f (p.nodes i))

def SupportingTrace (f : Fraction → Point) {a b : Fraction} (p : Partition a b)
    (cells : ∀ i, Cell (f (p.nodes i)) (f (p.nodes (i+1)))) (x : Point) : Prop :=
  ∃ i, i < p.count ∧ ∃ r, Meeting _ _ (cells i) r ∧
    (Segment (f (p.nodes i)) r x ∨ Segment r (f (p.nodes (i+1))) x)

theorem segment_left (p q : Point) : Segment p q p :=
  ⟨Fraction.ofInt 0, by constructor <;> decide, pointEquiv_symm (lerp_zero p q)⟩

theorem segment_right (p q : Point) : Segment p q q :=
  ⟨Fraction.ofInt 1, by constructor <;> decide, pointEquiv_symm (lerp_one p q)⟩

theorem between_left (u v : Fraction) : Between u u v := by
  by_cases h : Fraction.le u v
  · exact Or.inl ⟨Fraction.magnitudes.le_refl _, h⟩
  · exact Or.inr ⟨by unfold Fraction.le at *; omega, Fraction.magnitudes.le_refl _⟩

theorem between_right (u v : Fraction) : Between u v v := by
  by_cases h : Fraction.le u v
  · exact Or.inl ⟨h, Fraction.magnitudes.le_refl _⟩
  · exact Or.inr ⟨Fraction.magnitudes.le_refl _, by unfold Fraction.le at *; omega⟩

theorem affine_between_either (a u v : Fraction) (ha : UnitInterval a) :
    Between u (affine a u v) v := by
  by_cases h : Fraction.le u v
  · exact Or.inl (affine_between a u v ha h)
  · have hv : Fraction.le v u := by unfold Fraction.le at *; omega
    have hb := affine_between (complement a) v u (complement_interval a ha) hv
    have he : Fraction.equiv (affine a u v) (affine (complement a) v u) := by
      simp only [affine, complement, Fraction.equiv, Fraction.add, Fraction.mul,
        Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      ac_nf
      omega
    exact Or.inr ⟨Fraction.le_equiv_right hb.1 (Fraction.equiv_symm he),
      Fraction.le_equiv_left he hb.2⟩

theorem between_congr {u v x y : Fraction} (he : Fraction.equiv x y)
    (hy : Between u y v) : Between u x v := by
  rcases hy with hy | hy
  · exact Or.inl ⟨Fraction.le_equiv_right hy.1 (Fraction.equiv_symm he), Fraction.le_equiv_left he hy.2⟩
  · exact Or.inr ⟨Fraction.le_equiv_right hy.1 (Fraction.equiv_symm he), Fraction.le_equiv_left he hy.2⟩

theorem segment_rectangle (p q x : Point) (hx : Segment p q x) : RectangleBetween p x q := by
  obtain ⟨u, hu, he⟩ := hx
  exact ⟨between_congr he.1 (affine_between_either u p.1 q.1 hu),
    between_congr he.2 (affine_between_either u p.2 q.2 hu)⟩

theorem between_nested (a b u v x : Fraction) (hu : Between a u b) (hv : Between a v b)
    (hx : Between u x v) : Between a x b := by
  have oriented (l r z : Fraction) (hlr : Fraction.le l r) (hz : Between l z r) :
      Fraction.le l z ∧ Fraction.le z r := by
    rcases hz with hz | hz
    · exact hz
    · exact ⟨Fraction.magnitudes.le_trans hlr hz.1, Fraction.magnitudes.le_trans hz.2 hlr⟩
  have step (l r : Fraction) (hlu : Fraction.le l u ∧ Fraction.le u r)
      (hlv : Fraction.le l v ∧ Fraction.le v r) : Fraction.le l x ∧ Fraction.le x r := by
    rcases hx with hx | hx
    · exact ⟨Fraction.magnitudes.le_trans hlu.1 hx.1, Fraction.magnitudes.le_trans hx.2 hlv.2⟩
    · exact ⟨Fraction.magnitudes.le_trans hlv.1 hx.1, Fraction.magnitudes.le_trans hx.2 hlu.2⟩
  by_cases hab : Fraction.le a b
  · exact Or.inl (step a b (oriented a b u hab hu) (oriented a b v hab hv))
  · have hba : Fraction.le b a := by unfold Fraction.le at *; omega
    exact Or.inr (step b a (oriented b a u hba (hu.elim Or.inr Or.inl))
      (oriented b a v hba (hv.elim Or.inr Or.inl)))

theorem segment_rectangle_hull (p q u v x : Point) (hu : RectangleBetween p u q)
    (hv : RectangleBetween p v q) (hx : Segment u v x) : RectangleBetween p x q := by
  have hb := segment_rectangle u v x hx
  exact ⟨between_nested _ _ _ _ _ hu.1 hv.1 hb.1, between_nested _ _ _ _ _ hu.2 hv.2 hb.2⟩

theorem supporting_rectangle (p q : Point) (c : Cell p q) (r x : Point)
    (hr : Meeting p q c r) (hx : Segment p r x ∨ Segment r q x) : RectangleBetween p x q := by
  have hb := meeting_rectangle p q c r hr
  rcases hx with hx | hx
  · exact segment_rectangle_hull p q p r x ⟨between_left _ _, between_left _ _⟩ hb hx
  · exact segment_rectangle_hull p q r q x hb ⟨between_right _ _, between_right _ _⟩ hx

theorem segment_ball (p q anchor x : Point) (R : Fraction)
    (hp : Fraction.le (pointDistance p anchor) R)
    (hq : Fraction.le (pointDistance q anchor) R) (hx : Segment p q x) :
    Fraction.le (pointDistance x anchor) R := by
  obtain ⟨u, hu, he⟩ := hx
  exact Fraction.le_equiv_left (pointDistance_equiv he ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩)
    (lerp_ball_bound u hu anchor p q R hp hq)

theorem endpoint_zero_bound (p q : Point) :
    Fraction.le (pointDistance p p) (pointDistance q p) :=
  Fraction.le_equiv_left (pointDistance_self_zero p)
    (by simpa only [Fraction.le, Fraction.ofInt, Int.zero_mul, Int.mul_one]
      using pointNorm_nonnegative (pointSub q p))

theorem chord_cell_bound (p q x : Point) (hx : Segment p q x) :
    Fraction.le (pointDistance x p) (pointDistance q p) :=
  segment_ball p q p x _ (endpoint_zero_bound p q) (Fraction.magnitudes.le_refl _) hx

theorem supporting_cell_bound (p q : Point) (c : Cell p q) (r x : Point)
    (hr : Meeting p q c r) (hx : Segment p r x ∨ Segment r q x) :
    Fraction.le (pointDistance x p) (pointDistance q p) := by
  have hb := rectangle_distance_bound p r q (meeting_rectangle p q c r hr)
  rcases hx with hx | hx
  · exact segment_ball p r p x _ (endpoint_zero_bound p q) hb hx
  · exact segment_ball r q p x _ hb (Fraction.magnitudes.le_refl _) hx

/-- A common elementary estimate for all three finite boundary constructions.
The coverage of the parameter interval comes from the actual partition.
All nodes are values of the given curve, rather than a desired limit. -/
theorem enclosed_trace_approaches (f : Fraction → Point) (a b : Fraction)
    (parts : Nat → Partition a b) (hf : UniformOn f a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes (fun m => maxWidth (parts m)))
    (traces : Nat → Point → Prop)
    (hnodes : ∀ m i, i < (parts m).count → traces m (f ((parts m).nodes i)))
    (hbound : ∀ m x, traces m x → ∃ i, i < (parts m).count ∧
      Fraction.le (pointDistance x (f ((parts m).nodes i)))
        (pointDistance (f ((parts m).nodes (i+1))) (f ((parts m).nodes i)))) :
    Approaches traces (CurveTrace f a b) := by
  intro eps heps
  obtain ⟨delta, hd, hc⟩ := hf eps heps
  obtain ⟨N, hN⟩ := hmesh delta hd
  refine ⟨N, fun m hm => ?_⟩
  have hw (i : Nat) (hi : i < (parts m).count) :
      Fraction.le (durationDifference ((parts m).nodes i) ((parts m).nodes (i+1))).abs delta :=
    Fraction.magnitudes.le_trans
      (Fraction.le_equiv_left (Fraction.abs_of_nonnegative _
        ((difference_nonnegative_iff _ _).mpr ((parts m).ordered i hi)))
        ((maxWidth_bounds (parts m)).1 i hi))
      (Fraction.magnitudes.lt_implies_le (hN m hm))
  constructor
  · intro x hx
    obtain ⟨i, hi, hb⟩ := hbound m x hx
    have hlo := node_bounds (parts m) i (by omega)
    have hhi := node_bounds (parts m) (i+1) (by omega)
    refine ⟨f ((parts m).nodes i), ⟨(parts m).nodes i, hlo.1, hlo.2,
      ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩, ?_⟩
    have hnear := hc ((parts m).nodes i) ((parts m).nodes (i+1))
      hlo.1 hlo.2 hhi.1 hhi.2 (hw i hi)
    exact Fraction.magnitudes.lt_of_le_lt hb
      (Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_of_equiv (pointDistance_symm _ _)) hnear)
  · intro y hy
    obtain ⟨t, ht0, ht1, he⟩ := hy
    obtain ⟨i, hi, hl, hr⟩ := partition_cover (parts m) t ht0 ht1
    have hn := node_bounds (parts m) i (by omega)
    have ht := Fraction.magnitudes.le_trans
      (difference_interval_gaps _ _ _ hl hr).1 (hw i hi)
    refine ⟨f ((parts m).nodes i), hnodes m i hi, ?_⟩
    have hd' := hc _ _ hn.1 hn.2 ht0 ht1 ht
    have hs := Fraction.le_of_equiv (pointDistance_symm (f t) (f ((parts m).nodes i)))
    exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_equiv_left (pointDistance_equiv he
        ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩) hs) hd'

theorem rectangle_approaches (f : Fraction → Point) (a b : Fraction)
    (parts : Nat → Partition a b) (hf : UniformOn f a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes (fun m => maxWidth (parts m))) :
    Approaches (fun m => RectangleTrace f (parts m)) (CurveTrace f a b) := by
  apply enclosed_trace_approaches f a b parts hf hmesh
  · intro m i hi
    exact ⟨i, hi, between_left _ _, between_left _ _⟩
  · intro m x hx
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨i, hi, rectangle_distance_bound _ _ _ hx⟩

theorem nodes_approach (f : Fraction → Point) (a b : Fraction)
    (parts : Nat → Partition a b) (hf : UniformOn f a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes (fun m => maxWidth (parts m))) :
    Approaches (fun m => NodeTrace f (parts m)) (CurveTrace f a b) := by
  apply enclosed_trace_approaches f a b parts hf hmesh
  · exact fun m i hi => ⟨i, hi, Fraction.equiv_refl _, Fraction.equiv_refl _⟩
  · intro m x hx
    obtain ⟨i, hi, he⟩ := hx
    exact ⟨i, hi, Fraction.le_equiv_left
      (pointDistance_equiv he ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩) (endpoint_zero_bound _ _)⟩

/-- Finite set inclusion transfers the outer trace's forward estimate and
the inner trace's reverse estimate. This is not an area or arclength rule. -/
theorem trace_sandwich (inner middle outer : Nat → Point → Prop) (curve : Point → Prop)
    (hi : Approaches inner curve) (ho : Approaches outer curve)
    (him : ∀ m x, inner m x → middle m x) (hmo : ∀ m x, middle m x → outer m x) :
    Approaches middle curve := by
  intro eps heps
  obtain ⟨N, hN⟩ := hi eps heps
  obtain ⟨M, hM⟩ := ho eps heps
  refine ⟨N+M, fun m hm => ⟨?_, ?_⟩⟩
  · exact fun x hx => (hM m (by omega)).1 x (hmo m x hx)
  · intro y hy
    obtain ⟨x, hx, hd⟩ := (hN m (by omega)).2 y hy
    exact ⟨x, him m x hx, hd⟩

theorem nodes_in_chords (f : Fraction → Point) {a b : Fraction} (p : Partition a b)
    (x : Point) (hx : NodeTrace f p x) : ChordTrace f p x := by
  obtain ⟨i, hi, he⟩ := hx
  exact ⟨i, hi, Fraction.ofInt 0, by constructor <;> decide,
    pointEquiv_trans he (pointEquiv_symm (lerp_zero _ _))⟩

theorem chords_in_rectangles (f : Fraction → Point) {a b : Fraction} (p : Partition a b)
    (x : Point) (hx : ChordTrace f p x) : RectangleTrace f p x := by
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨i, hi, segment_rectangle _ _ x hx⟩

theorem nodes_in_supporting (f : Fraction → Point) {a b : Fraction} (p : Partition a b)
    (cells : ∀ i, Cell (f (p.nodes i)) (f (p.nodes (i+1))))
    (x : Point) (hx : NodeTrace f p x) : SupportingTrace f p cells x := by
  obtain ⟨i, hi, he⟩ := hx
  obtain ⟨r, hr⟩ := meeting_exists _ _ (cells i)
  exact ⟨i, hi, r, hr, Or.inl ⟨Fraction.ofInt 0, by constructor <;> decide,
    pointEquiv_trans he (pointEquiv_symm (lerp_zero _ _))⟩⟩

theorem supporting_in_rectangles (f : Fraction → Point) {a b : Fraction} (p : Partition a b)
    (cells : ∀ i, Cell (f (p.nodes i)) (f (p.nodes (i+1))))
    (x : Point) (hx : SupportingTrace f p cells x) : RectangleTrace f p x := by
  obtain ⟨i, hi, r, hr, hx⟩ := hx
  exact ⟨i, hi, supporting_rectangle _ _ (cells i) r x hr hx⟩

end NewtonLimitDynamics.Polygon.RationalBoundary
