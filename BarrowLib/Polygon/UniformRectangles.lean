import BarrowLib.Polygon.MagnitudeContent
import BarrowLib.Polygon.RationalBoundary

/-! Rectangular exhaustion of a nonnegative uniformly continuous rational
graph, without a monotonicity premise. The precise statements and elementary
finite proofs here are project derivations; no exact external theorem or
historical priority is claimed. Their class follows their Barrow dependencies.

This is an editorial extension of the figure scope of Newton's Lemmas II–III,
not his printed telescoping proof. His exact Latin and edition-local clients
remain in the historical files. Uniform continuity is explicit, not attributed
to Newton as a quoted hypothesis. Finite rectangles and their areas are
constructed using the existing partial area rules. Curved-area existence,
nonrational coordinates, tangents and general patch assembly are not supplied
by this construction. The earlier X.1 magnitude premise remains visible. -/

namespace NewtonLimitDynamics.Polygon.UniformRectangles
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles PolygonFanArea
open HarmonicTimeComparison HarmonicTimeRealization

/-- Lower height clipped at the fixed baseline; it may be zero near a zero
of the graph. The upper height is `H+eps`. Neither is an assumed extremum. -/
noncomputable def lower (H eps : Fraction) : Fraction := by
  classical
  exact if Fraction.le eps H then durationDifference eps H else Fraction.ofInt 0

def upper (H eps : Fraction) : Fraction := Fraction.add H eps

/-- A positive ordinate before the right endpoint and uniform continuity
construct a nonzero rectangle inside the figure, even when the graph falls
elsewhere. This exact statement and proof are project provenance; no area
assignment or historical continuity hypothesis is inferred. -/
theorem positive_rectangle (g : Fraction → Fraction) (a b c : Fraction)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b) :
    ∃ r : Fraction, Fraction.lt c r ∧ Fraction.le r b ∧
      ∀ x, rectangle c r (g c).half x → figure g a b x := by
  obtain ⟨delta,hdelta,hnear⟩ := hf (g c).half hgc
  let r := Fraction.ofRat (c.toRat + min ((b.toRat-c.toRat)/2) delta.toRat)
  have hcbR := (Fraction.lt_iff_toRat c b).mp hcb
  have hdR := (Fraction.positive_iff_toRat delta).mp hdelta
  have hr : c.toRat < r.toRat ∧ r.toRat ≤ b.toRat ∧ r.toRat-c.toRat ≤ delta.toRat := by
    dsimp only [r]
    rw [Fraction.toRat_ofRat]
    grind
  refine ⟨r,(Fraction.lt_iff_toRat c r).mpr hr.1,
    (Fraction.le_iff_toRat r b).mpr hr.2.1,?_⟩
  rintro x ⟨hcx,hxr,hyzero,hy⟩
  have hax := Fraction.magnitudes.le_trans hac hcx
  have hxb := Fraction.magnitudes.le_trans hxr ((Fraction.le_iff_toRat r b).mpr hr.2.1)
  have hdist : Fraction.le (durationDifference c x.1).abs delta := by
    apply (Fraction.le_iff_toRat _ _).mpr
    rw [Fraction.toRat_abs,Fraction.toRat_durationDifference]
    have hxR := (Fraction.le_iff_toRat c x.1).mp hcx
    have hxrR := (Fraction.le_iff_toRat x.1 r).mp hxr
    rw [Rat.abs_of_nonneg (by grind)]
    grind
  have hc := hnear c x.1 hac (Fraction.magnitudes.lt_implies_le hcb) hax hxb hdist
  have hyabs : Fraction.le (durationDifference (g x.1) (g c)).abs
      (FiniteEstimates.pointDistance (c,g c) (x.1,g x.1)) :=
    Fraction.le_equiv_right
      (Fraction.le_add_nonnegative _ (durationDifference x.1 c).abs
        (Fraction.abs_num_nonnegative _)) (Fraction.add_comm _ _)
  have hsum := difference_add_bound (g x.1) (g c) (g c).half
    (Fraction.magnitudes.le_trans (Fraction.le_abs _)
      (Fraction.magnitudes.lt_implies_le (Fraction.magnitudes.lt_of_le_lt hyabs hc)))
  have hheight : Fraction.le (g c).half (g x.1) :=
    Fraction.le_add_cancel_left (g c).half _ _
      (Fraction.le_equiv_left (Fraction.half_add_self (g c))
        (Fraction.le_equiv_right hsum (Fraction.add_comm _ _)))
  exact ⟨hax,hxb,hyzero,Fraction.magnitudes.le_trans hy hheight⟩

private theorem lower_properties (H eps : Fraction) (hH : 0≤H.num) (heps : 0≤eps.num) :
    0≤(lower H eps).num ∧ Fraction.le (lower H eps) H ∧
      Fraction.le H (Fraction.add (lower H eps) eps) := by
  classical
  unfold lower
  split
  · rename_i h
    have he : Fraction.equiv (Fraction.add (durationDifference eps H) eps) H :=
      Fraction.equiv_trans (Fraction.add_comm _ _) (add_difference_cancel eps H)
    exact ⟨(difference_nonnegative_iff _ _).mpr h,
      Fraction.le_equiv_right (Fraction.le_add_nonnegative _ eps heps) he,
      Fraction.le_of_equiv (Fraction.equiv_symm he)⟩
  · rename_i h
    have hHe : Fraction.le H eps := by unfold Fraction.le at *; omega
    refine ⟨by decide,?_,?_⟩
    · simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hH
    · exact Fraction.le_equiv_right hHe
        (Fraction.equiv_symm (Fraction.equiv_trans (Fraction.add_comm _ _) (Fraction.add_zero eps)))

private theorem height_enclosure (H v eps : Fraction) (hv : 0≤v.num)
    (hvH : Fraction.le (durationDifference v H).abs eps) :
    Fraction.le (lower H eps) v ∧ Fraction.le v (upper H eps) := by
  have hvupper := difference_add_bound H v eps
    (Fraction.magnitudes.le_trans (Fraction.le_abs _)
      (Fraction.le_equiv_left (durationDifference_abs_symm H v) hvH))
  refine ⟨?_,hvupper⟩
  classical
  unfold lower
  split
  · have hHupper := difference_add_bound v H eps
      (Fraction.magnitudes.le_trans (Fraction.le_abs _) hvH)
    exact Fraction.le_add_cancel_left eps _ v
      (Fraction.le_equiv_left (add_difference_cancel eps H)
        (Fraction.le_equiv_right hHupper (Fraction.add_comm v eps)))
  · simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hv

private theorem height_distances (t H eps : Fraction) (hH : 0≤H.num) (heps : 0≤eps.num) :
    Fraction.le (FiniteEstimates.pointDistance (t,lower H eps) (t,H)) eps ∧
      Fraction.le (FiniteEstimates.pointDistance (t,upper H eps) (t,H)) eps := by
  have hp := lower_properties H eps hH heps
  have hlo := (Fraction.le_iff_toRat _ _).mp hp.2.1
  have hsum := (Fraction.le_iff_toRat _ _).mp hp.2.2
  rw [Fraction.toRat_add] at hsum
  have he := (Fraction.nonnegative_iff_toRat eps).mp heps
  constructor
  · change Fraction.le (Fraction.add (durationDifference t t).abs
      (durationDifference H (lower H eps)).abs) eps
    apply (Fraction.le_iff_toRat _ _).mpr
    simp only [Fraction.toRat_add,Fraction.toRat_abs,Fraction.toRat_durationDifference,
      Rat.sub_self,Rat.abs_zero,Rat.zero_add]
    rw [Rat.abs_of_nonpos (by grind only)]
    grind only
  · change Fraction.le (Fraction.add (durationDifference t t).abs
      (durationDifference H (upper H eps)).abs) eps
    apply (Fraction.le_iff_toRat _ _).mpr
    simp only [Fraction.toRat_add,Fraction.toRat_abs,Fraction.toRat_durationDifference,
      Rat.sub_self,Rat.abs_zero,Rat.zero_add,upper,Fraction.toRat_add]
    rw [Rat.abs_of_nonneg (by grind only)]
    grind only

private theorem height_gap (H eps : Fraction) (hH : 0≤H.num) (heps : 0≤eps.num) :
    Fraction.le (durationDifference (lower H eps) (upper H eps))
      (Fraction.add eps eps) := by
  have hp := lower_properties H eps hH heps
  have hU := Fraction.le_equiv_right (Fraction.add_le_add_right hp.2.2 eps)
    (Fraction.add_assoc (lower H eps) eps eps)
  exact Fraction.le_add_cancel_left (lower H eps) _ _
    (Fraction.le_equiv_left (add_difference_cancel _ _) hU)

def value {a b : Fraction} (p : Partition a b) (heights : Nat → Fraction) : Fraction :=
  sum (fun i => Fraction.mul (width p i) (heights i)) p.count

noncomputable def lowerHeights {a b : Fraction} (g : Fraction → Fraction)
    (p : Partition a b) (eps : Fraction) : Nat → Fraction :=
  fun i => lower (g (p.nodes i)) eps

def upperHeights {a b : Fraction} (g : Fraction → Fraction)
    (p : Partition a b) (eps : Fraction) : Nat → Fraction :=
  fun i => upper (g (p.nodes i)) eps

/-- Tops and internal joins belong to their actual rectangle union even
when adjacent heights fall. A join uses the higher of its adjacent cells.
This project derivation does not assert graph enclosure or area existence. -/
theorem staircase_in_strips (h : Fraction → Fraction) {a b : Fraction}
    (p : Partition a b) (hn : ∀ i, i<p.count → 0≤(h (p.nodes i)).num)
    (x : Point) (hx : RationalBoundary.LowerStaircase h p x) :
    RectangleContent.strips p (fun i => h (p.nodes i)) p.count x := by
  obtain ⟨i,hi,hx⟩ := hx
  rcases hx with hx | ⟨hnext,he,hbetween⟩
  · exact ⟨i,hi,hx.1,hx.2.1,Fraction.nonnegative_equiv hx.2.2 (hn i hi),
      Fraction.le_of_equiv hx.2.2⟩
  · rcases hbetween with h | h
    · exact ⟨i+1,hnext,Fraction.le_equiv_right
        (Fraction.magnitudes.le_refl _) (Fraction.equiv_symm he),
        Fraction.le_equiv_left he (p.ordered (i+1) hnext),
        Fraction.nonnegative_of_le (hn i hi) h.1,h.2⟩
    · exact ⟨i,hi,Fraction.le_equiv_right (p.ordered i hi) (Fraction.equiv_symm he),
        Fraction.le_of_equiv he,Fraction.nonnegative_of_le (hn (i+1) hnext) h.1,h.2⟩

/-- Two-sided approach and actual-union membership of both free step traces.
The upper construction also uses left samples, with height g(node)+eps;
both traces therefore use the internal-join convention of LowerStaircase. -/
def StaircaseApproximation (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → Partition a b) (eps : Nat → Fraction) : Prop :=
  RationalBoundary.Approaches
    (fun m => RationalBoundary.LowerStaircase (fun t => lower (g t) (eps m)) (parts m))
    (RationalBoundary.CurveTrace (fun t => (t,g t)) a b) ∧
  RationalBoundary.Approaches
    (fun m => RationalBoundary.LowerStaircase (fun t => upper (g t) (eps m)) (parts m))
    (RationalBoundary.CurveTrace (fun t => (t,g t)) a b) ∧
  ∀ m x, (RationalBoundary.LowerStaircase (fun t => lower (g t) (eps m)) (parts m) x →
    RectangleContent.strips (parts m) (lowerHeights g (parts m) (eps m)) (parts m).count x) ∧
    (RationalBoundary.LowerStaircase (fun t => upper (g t) (eps m)) (parts m) x →
      RectangleContent.strips (parts m) (upperHeights g (parts m) (eps m)) (parts m).count x)

/-- Free edges of the same clipped lower/upper rectangle constructions
approach a nonnegative uniformly continuous graph in both directions.
The nonnegative errors and mesh shrink separately; no monotonicity or area
assignment is required. Enclosure, when needed, additionally uses the fine
mesh condition of fine_rectangles. Fixed baseline/endpoint sides and
topological perimeter are not asserted. Exact project derivation. -/
theorem staircase_approaches (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → Partition a b) (eps : Nat → Fraction)
    (heps : ∀ m, 0≤(eps m).num)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes (fun m => maxWidth (parts m)))
    (hvanish : Exhaustion.VanishingDifference Fraction.magnitudes eps) :
    StaircaseApproximation g a b parts eps := by
  have hn (m i : Nat) (hi : i≤(parts m).count) : 0≤(g ((parts m).nodes i)).num :=
    hzero _ (node_bounds (parts m) i hi).1 (node_bounds (parts m) i hi).2
  refine ⟨?_,?_,fun m x => ⟨?_,?_⟩⟩
  · apply RationalBoundary.perturbed_trace_approaches (fun t => (t,g t)) a b parts hf hmesh
      (fun m t => (t,lower (g t) (eps m))) eps
      (fun m i hi => (height_distances _ _ _ (hn m i hi) (heps m)).1) hvanish
    · intro m i hi
      exact RationalBoundary.nodes_in_lower_staircase _ _ _
        ⟨i,hi,Fraction.equiv_refl _,Fraction.equiv_refl _⟩
    · exact fun m => RationalBoundary.lower_staircase_in_rectangles _ _
  · apply RationalBoundary.perturbed_trace_approaches (fun t => (t,g t)) a b parts hf hmesh
      (fun m t => (t,upper (g t) (eps m))) eps
      (fun m i hi => (height_distances _ _ _ (hn m i hi) (heps m)).2) hvanish
    · intro m i hi
      exact RationalBoundary.nodes_in_lower_staircase _ _ _
        ⟨i,hi,Fraction.equiv_refl _,Fraction.equiv_refl _⟩
    · exact fun m => RationalBoundary.lower_staircase_in_rectangles _ _
  · exact staircase_in_strips (fun t => lower (g t) (eps m)) (parts m)
      (fun i hi => (lower_properties _ _ (hn m i (by omega)) (heps m)).1) x
  · exact staircase_in_strips (fun t => upper (g t) (eps m)) (parts m)
      (fun i hi => Fraction.nonnegative_add (g ((parts m).nodes i)) (eps m)
        (hn m i (by omega)) (heps m)) x

/-- Finite rectangular sets and gap control for any two cell-height bounds.
The bounds concern graph ordinates, not areas or convergence conclusions. -/
def Encloses {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q) (p : Partition a b)
    (lo hi : Nat → Fraction) : Prop :=
  (∀ x, RectangleContent.strips p lo p.count x → figure g a b x) ∧
    (∀ x, figure g a b x → RectangleContent.strips p hi p.count x) ∧
    area.HasArea (RectangleContent.strips p lo p.count) (area.magnitudes.embed (value p lo)) ∧
    area.HasArea (RectangleContent.strips p hi p.count) (area.magnitudes.embed (value p hi)) ∧
    area.magnitudes.order.le (area.magnitudes.embed (value p lo)) A ∧
    area.magnitudes.order.le A (area.magnitudes.embed (value p hi))

theorem rectangle_enclosure {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q) (p : Partition a b)
    (lo hi : Nat → Fraction) (hlo : ∀ i, i<p.count → 0≤(lo i).num)
    (hhi : ∀ i, i<p.count → 0≤(hi i).num)
    (hbounds : ∀ i, i<p.count → ∀ t, Fraction.le (p.nodes i) t →
      Fraction.le t (p.nodes (i+1)) → Fraction.le (lo i) (g t) ∧ Fraction.le (g t) (hi i))
    (hA : area.HasArea (figure g a b) A) :
    Encloses area g a b A p lo hi := by
  have hL := RectangleContent.strips_area (MagnitudeContent.rationalAreas area)
    p lo hlo p.count (Nat.le_refl _)
  have hU := RectangleContent.strips_area (MagnitudeContent.rationalAreas area)
    p hi hhi p.count (Nat.le_refl _)
  have hsetsL : ∀ x, RectangleContent.strips p lo p.count x → figure g a b x := by
    rintro x ⟨i,hi',hl,hr,hzero,hy⟩
    exact ⟨Fraction.magnitudes.le_trans (node_bounds p i (by omega)).1 hl,
      Fraction.magnitudes.le_trans hr (node_bounds p (i+1) (by omega)).2,hzero,
      Fraction.magnitudes.le_trans hy (hbounds i hi' x.1 hl hr).1⟩
  have hsetsU : ∀ x, figure g a b x → RectangleContent.strips p hi p.count x := by
    rintro x ⟨ha,hb,hzero,hy⟩
    obtain ⟨i,hi',hl,hr⟩ := partition_cover p x.1 ha hb
    exact ⟨i,hi',hl,hr,hzero,Fraction.magnitudes.le_trans hy (hbounds i hi' x.1 hl hr).2⟩
  exact ⟨hsetsL,hsetsU,hL,hU,area.monotone _ _ _ _ hsetsL hL hA,
    area.monotone _ _ _ _ hsetsU hA hU⟩

private theorem value_gap_bound {a b : Fraction} (p : Partition a b)
    (lo hi : Nat → Fraction) (E : Fraction)
    (hbounds : ∀ i, i<p.count → Fraction.le (durationDifference (lo i) (hi i)) E) :
    Fraction.le (durationDifference (value p lo) (value p hi))
      (Fraction.mul E (durationDifference a b)) := by
  have he : Fraction.equiv (durationDifference (value p lo) (value p hi))
      (sum (fun i => Fraction.mul (width p i) (durationDifference (lo i) (hi i))) p.count) := by
    apply Fraction.equiv_trans (sum_difference _ _ p.count)
    apply sum_congr
    intro i
    simp only [sub,neg,durationDifference,HarmonicStability.negF,Fraction.equiv,
      Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf
  have hsum := sum_mono _ (fun i => Fraction.mul E (width p i)) p.count (fun i hi' =>
    Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative_left (hbounds i hi')
      (width p i) ((difference_nonnegative_iff _ _).mpr (p.ordered i hi')))
      (Fraction.mul_comm _ _))
  exact Fraction.le_equiv_left he (Fraction.le_equiv_right hsum
    (Fraction.equiv_trans (sum_mul (width p) E p.count)
      (Fraction.mul_equiv_left E (Fraction.equiv_trans (sum_telescope p.nodes p.count)
        (difference_congr p.first p.last)))))

/-- Uniform continuity constructs genuine lower/upper rectangles on every
sufficiently fine partition, without extrema or monotonicity of the graph.
The total gap is at most twice the height tolerance times the interval width.
This is a project derivation, not Newton's telescoping gap identity. -/
theorem fine_rectangles {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (figure g a b) A) (eps : Fraction) (heps : 0<eps.num) :
    ∃ delta : Fraction, 0<delta.num ∧ ∀ p : Partition a b, Fraction.lt (maxWidth p) delta →
      Encloses area g a b A p (lowerHeights g p eps) (upperHeights g p eps) ∧
      Fraction.le (durationDifference (value p (lowerHeights g p eps))
        (value p (upperHeights g p eps)))
        (Fraction.mul (Fraction.add eps eps) (durationDifference a b)) := by
  obtain ⟨delta,hdelta,hfdelta⟩ := hf eps heps
  refine ⟨delta,hdelta,fun p hp => ?_⟩
  have hn (i : Nat) (hi : i<p.count) : 0≤(g (p.nodes i)).num :=
    hzero _ (node_bounds p i (by omega)).1 (node_bounds p i (by omega)).2
  have hbounds (i : Nat) (hi : i<p.count) (t : Fraction)
      (hl : Fraction.le (p.nodes i) t) (hr : Fraction.le t (p.nodes (i+1))) :
      Fraction.le (lowerHeights g p eps i) (g t) ∧
        Fraction.le (g t) (upperHeights g p eps i) := by
    have ht : Fraction.le a t ∧ Fraction.le t b :=
      ⟨Fraction.magnitudes.le_trans (node_bounds p i (by omega)).1 hl,
      Fraction.magnitudes.le_trans hr (node_bounds p (i+1) (by omega)).2⟩
    have hdist := Fraction.magnitudes.le_trans
      (Fraction.le_equiv_right (difference_interval_gaps _ _ _ hl hr).1
        (Fraction.abs_of_nonnegative _ ((difference_nonnegative_iff _ _).mpr (p.ordered i hi))))
      (Fraction.magnitudes.le_trans ((maxWidth_bounds p).1 i hi)
        (Fraction.magnitudes.lt_implies_le hp))
    have hc := hfdelta (p.nodes i) t (node_bounds p i (by omega)).1
      (node_bounds p i (by omega)).2 ht.1 ht.2 hdist
    have hy : Fraction.le (durationDifference (g t) (g (p.nodes i))).abs
        (FiniteEstimates.pointDistance (p.nodes i,g (p.nodes i)) (t,g t)) :=
      Fraction.le_equiv_right
        (Fraction.le_add_nonnegative _ (durationDifference t (p.nodes i)).abs
          (Fraction.abs_num_nonnegative _)) (Fraction.add_comm _ _)
    exact height_enclosure _ _ eps (hzero t ht.1 ht.2)
      (Fraction.magnitudes.lt_implies_le (Fraction.magnitudes.lt_of_le_lt hy hc))
  exact ⟨rectangle_enclosure area g a b A p _ _
      (fun i hi => (lower_properties _ eps (hn i hi) (Int.le_of_lt heps)).1)
      (fun i hi => Fraction.nonnegative_add _ eps (hn i hi) (Int.le_of_lt heps)) hbounds hA,
    value_gap_bound p _ _ _ (fun i hi => height_gap _ eps (hn i hi) (Int.le_of_lt heps))⟩

/-- One actual succession of rectangle unions has simultaneous enclosure,
shrinking area gap, assigned-area error decay and free-edge approximation.
Indices increase strictly, retaining the order of the supplied subdivisions;
nesting is not asserted unless the supplied subdivisions have that property.
The selected partitions are paired with eps m, not eps (indices m).
This packages conclusions, not additional geometric or limiting premises. -/
def MatchedApproximation {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q)
    (parts : Nat → Partition a b) (eps : Nat → Fraction) (indices : Nat → Nat) : Prop :=
  (∀ m, m≤indices m) ∧ (∀ m, indices m<indices (m+1)) ∧
  let selected := fun m => parts (indices m)
  let L := fun m => value (selected m) (lowerHeights g (selected m) (eps m))
  let U := fun m => value (selected m) (upperHeights g (selected m) (eps m))
  Exhaustion.VanishingDifference Fraction.magnitudes (fun m => maxWidth (selected m)) ∧
    (∀ m, Encloses area g a b A (selected m)
      (lowerHeights g (selected m) (eps m)) (upperHeights g (selected m) (eps m))) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes (fun m => durationDifference (L m) (U m)) ∧
    MagnitudeContent.ErrorsVanish area.magnitudes L U A ∧
    StaircaseApproximation g a b selected eps

/-- Select a single matched family from any shrinking mesh and positive
vanishing height tolerances. Continuity constructs the required coupling:
no enclosure, area-error limit or boundary limit is assumed. The gap bound
2*eps*(b-a) gives area decay on this same family. This exact statement and
derivation are project provenance, without historical textual attribution.
Classical choice gives existential indices, not an executable index algorithm.
Curved-area existence remains supplied; fixed sides remain outside the trace. -/
theorem matched_approximation {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q)
    (parts : Nat → Partition a b) (eps : Nat → Fraction)
    (heps : ∀ m, 0<(eps m).num) (hab : Fraction.le a b)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (figure g a b) A)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes (fun m => maxWidth (parts m)))
    (hvanish : Exhaustion.VanishingDifference Fraction.magnitudes eps) :
    ∃ indices, MatchedApproximation area g a b A parts eps indices := by
  classical
  have choices (m : Nat) : ∃ N, ∀ k, N≤k →
      Encloses area g a b A (parts k)
        (lowerHeights g (parts k) (eps m)) (upperHeights g (parts k) (eps m)) ∧
      Fraction.le (durationDifference
        (value (parts k) (lowerHeights g (parts k) (eps m)))
        (value (parts k) (upperHeights g (parts k) (eps m))))
        (Fraction.mul (Fraction.add (eps m) (eps m)) (durationDifference a b)) := by
    obtain ⟨delta,hd,hfine⟩ := fine_rectangles area g a b A hzero hf hA (eps m) (heps m)
    obtain ⟨N,hN⟩ := hmesh delta hd
    exact ⟨N,fun k hk => hfine (parts k) (hN k hk)⟩
  let cutoff := fun m => Classical.choose (choices m)
  let indices : Nat → Nat := Nat.rec (cutoff 0)
    (fun m previous => max (previous+1) (cutoff (m+1)))
  have hindices (m : Nat) : m≤indices m ∧ cutoff m≤indices m := by
    induction m with
    | zero => exact ⟨Nat.zero_le _,Nat.le_refl _⟩
    | succ m ih =>
      change m+1≤max (indices m+1) (cutoff (m+1)) ∧
        cutoff (m+1)≤max (indices m+1) (cutoff (m+1))
      omega
  have hincrease (m : Nat) : indices m<indices (m+1) := by
    change indices m<max (indices m+1) (cutoff (m+1))
    omega
  let selected := fun m => parts (indices m)
  let L := fun m => value (selected m) (lowerHeights g (selected m) (eps m))
  let U := fun m => value (selected m) (upperHeights g (selected m) (eps m))
  have hfinite (m : Nat) := Classical.choose_spec (choices m) (indices m) (hindices m).2
  have hselected : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => maxWidth (selected m)) := by
    intro d hd
    obtain ⟨N,hN⟩ := hmesh d hd
    exact ⟨N,fun m hm => hN (indices m) (by have := (hindices m).1; omega)⟩
  have hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => durationDifference (L m) (U m)) := by
    intro d hd
    let C : Rat := 2*(b.toRat-a.toRat)
    have habR := (Fraction.le_iff_toRat _ _).mp hab
    have hC : 0≤C := by dsimp only [C]; grind only
    have hhalf := (Fraction.positive_iff_toRat d.half).mp hd
    let eta := Fraction.ofRat (factorDelta C d.half.toRat hC)
    have heta : 0<eta.num := by
      apply (Fraction.positive_iff_toRat _).mpr
      change 0<(Fraction.ofRat _).toRat
      rw [Fraction.toRat_ofRat]
      grind only [factorDelta,Rat.div_def,Rat.inv_pos,Rat.mul_pos]
    obtain ⟨N,hN⟩ := hvanish eta heta
    refine ⟨N,fun m hm => ?_⟩
    have hsmall := (Fraction.lt_iff_toRat _ _).mp (hN m hm)
    change (eps m).toRat<(Fraction.ofRat _).toRat at hsmall
    rw [Fraction.toRat_ofRat] at hsmall
    have hscaled := Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hsmall) hC)
      (factor_delta_weak C d.half.toRat hC (Rat.le_of_lt hhalf))
    have hb := (Fraction.le_iff_toRat _ _).mp (hfinite m).2
    simp only [Fraction.toRat_mul,Fraction.toRat_add,Fraction.toRat_durationDifference] at hb
    have hbound : (durationDifference (L m) (U m)).toRat≤(eps m).toRat*C := by
      have he : ((eps m).toRat+(eps m).toRat)*(b.toRat-a.toRat)=(eps m).toRat*C := by
        dsimp only [C]
        grind only
      rw [Fraction.toRat_durationDifference,←he]
      exact hb
    exact Fraction.magnitudes.lt_of_le_lt
      ((Fraction.le_iff_toRat _ _).mpr (Rat.le_trans hbound hscaled)) (Fraction.half_lt d hd)
  refine ⟨indices,fun m => (hindices m).1,hincrease,hselected,
    fun m => (hfinite m).1,hgap,?_,?_⟩
  · exact MagnitudeContent.errors_vanish area.magnitudes L U A
      (fun m => (hfinite m).1.2.2.2.2) hgap
  · exact staircase_approaches g a b selected eps (fun m => Int.le_of_lt (heps m))
      hzero hf hselected hvanish

/-- On every sufficiently fine subdivision there are actual enclosing
rectangle unions whose gap and both assigned-area errors are below the
given magnitude tolerance. The height tolerance is constructed too.
The statement concerns all fine partitions, rather than a selected subsequence.
Curved-area existence and the classical area/magnitude rules remain explicit. -/
def Exhausts {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q) : Prop :=
  ∀ d, area.magnitudes.order.positive d →
    ∃ eps delta : Fraction, 0<eps.num ∧ 0<delta.num ∧
      ∀ p : Partition a b, Fraction.lt (maxWidth p) delta →
        Encloses area g a b A p (lowerHeights g p eps) (upperHeights g p eps) ∧
        area.magnitudes.order.lt (area.magnitudes.embed
          (durationDifference (value p (lowerHeights g p eps)) (value p (upperHeights g p eps)))) d ∧
        area.magnitudes.order.lt A
          (area.magnitudes.add (area.magnitudes.embed (value p (lowerHeights g p eps))) d) ∧
        area.magnitudes.order.lt (area.magnitudes.embed (value p (upperHeights g p eps)))
          (area.magnitudes.add A d)

theorem exhaustion {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q)
    (hab : Fraction.le a b)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (figure g a b) A) : Exhausts area g a b A := by
  intro d hd
  obtain ⟨j,hj⟩ := area.magnitudes.unit_halves_exhaust d hd
  let q := HarmonicDyadic.duration (Fraction.ofInt 1) j
  have hq : 0<q.num := by change (0 : Int)<1; decide
  let C := Fraction.mul (Fraction.ofInt 2) (durationDifference a b)
  have hC : 0≤C.num := Fraction.nonnegative_mul _ _ (by decide)
    ((difference_nonnegative_iff _ _).mpr hab)
  let eps := (Fraction.ofRat (factorDelta (C).toRat (q).toRat ((Fraction.nonnegative_iff_toRat C).mp hC))).half
  have heps : 0<eps.num := (by
      change 0 < (Fraction.ofRat (factorDelta C.toRat q.toRat ((Fraction.nonnegative_iff_toRat C).mp hC))).num
      apply (Fraction.positive_iff_toRat _).mpr
      change 0 < (Fraction.ofRat _).toRat
      rw [Fraction.toRat_ofRat]
      have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
      have hepsRat : 0 < (q).toRat := (Fraction.positive_iff_toRat (q)).mp hq
      (try dsimp only at hcoef hepsRat ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos])
  obtain ⟨delta,hdelta,hfine⟩ := fine_rectangles area g a b A hzero hf hA eps heps
  refine ⟨eps,delta,heps,hdelta,fun p hp => ?_⟩
  obtain ⟨henclose,hbound⟩ := hfine p hp
  have he : Fraction.equiv (Fraction.mul (Fraction.add eps eps) (durationDifference a b))
      (Fraction.mul eps C) := by
    simp only [C,Fraction.equiv,Fraction.mul,Fraction.add,Fraction.ofInt,
      Int.one_mul,Int.add_mul]
    simp only [show (2 : Int) = 1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul]
    ac_nf
  have hsmall := Fraction.magnitudes.lt_of_le_lt (Fraction.le_equiv_right hbound he)
    ((show Fraction.lt (Fraction.mul (eps) (C)) (q) from by
        apply (Fraction.lt_iff_toRat _ _).mpr
        rw [Fraction.toRat_mul]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hdist := ((Fraction.nonnegative_iff_toRat eps).mp (Int.le_of_lt heps))
        have hstrict := (Fraction.lt_iff_toRat _ _).mp (Fraction.half_lt (Fraction.ofRat (factorDelta (C).toRat (q).toRat ((Fraction.nonnegative_iff_toRat C).mp hC))) ((by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hepsRat : 0 < (q).toRat := (Fraction.positive_iff_toRat (q)).mp hq
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos])))
        change Fraction.toRat _ < (Fraction.ofRat _).toRat at hstrict
        rw [Fraction.toRat_ofRat] at hstrict
        (try dsimp only at hcoef hdist hstrict ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff]))
  have hgap := area.magnitudes.order.lt_of_le_lt
    ((area.magnitudes.embed_le _ _).mpr (Fraction.magnitudes.lt_implies_le hsmall)) hj
  exact ⟨henclose,hgap,MagnitudeContent.enclosure_errors_lt area.magnitudes _ _ A d
    henclose.2.2.2.2 hgap⟩

/-- For each fixed unequal positive integer pair, every sufficiently fine
partition has actual enclosing rectangle unions giving the unit-ratio
comparisons for any two magnitudes between their areas. In particular these
are all three lower/upper/assigned-area comparisons, with no division of Q.
Every positive height tolerance below the returned cutoff is admitted;
its required mesh threshold may depend on that tolerance. -/
def RatiosExhaust {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (g : Fraction → Fraction) (a b : Fraction) (A : Q) : Prop :=
  ∀ n m : Nat, 0<n → n<m →
    ∃ cutoff : Fraction, 0<cutoff.num ∧
      ∀ eps : Fraction, 0<eps.num → Fraction.le eps cutoff →
        ∃ delta : Fraction, 0<delta.num ∧
          ∀ p : Partition a b, Fraction.lt (maxWidth p) delta →
            Encloses area g a b A p (lowerHeights g p eps) (upperHeights g p eps) ∧
            MagnitudeContent.BracketComparisons area.magnitudes n m
              (value p (lowerHeights g p eps)) (value p (upperHeights g p eps))

/-- A constructed positive rectangle supplies the denominator control for
nonmonotone graphs. Finite gap control then gives the comparisons for all
fine partitions, not just a selected subsequence. Curved area and the area
and multiple rules remain supplied; no ratio-limit premise is added.
Provenance: this exact project statement and checked derivation. -/
theorem ratios_exhaustion {Q : Type} (area : MagnitudeContent.AreaRules Q)
    (multiples : MagnitudeContent.MultipleRules area.magnitudes)
    (g : Fraction → Fraction) (a b c : Fraction) (A : Q)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hzero : ∀ t, Fraction.le a t → Fraction.le t b → 0≤(g t).num)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (hA : area.HasArea (figure g a b) A) : RatiosExhaust area g a b A := by
  obtain ⟨r,hcr,hrb,hrect⟩ := positive_rectangle g a b c hac hcb hgc hf
  let R := Fraction.mul (durationDifference c r) (g c).half
  have hRR : 0<R.toRat := by
    dsimp only [R]
    rw [Fraction.toRat_mul,Fraction.toRat_durationDifference,Fraction.toRat_half]
    have hcrR := (Fraction.lt_iff_toRat c r).mp hcr
    have hgcR := (Fraction.positive_iff_toRat (g c)).mp hgc
    apply Rat.mul_pos <;> grind
  have hR : 0<R.num := (Fraction.positive_iff_toRat R).mpr hRR
  have hRA : area.magnitudes.order.le (area.magnitudes.embed R) A :=
    area.monotone _ _ _ _ hrect
      (area.rectangle c r (g c).half (Fraction.magnitudes.lt_implies_le hcr)
        (Int.le_of_lt hgc)) hA
  have hwidth : 0≤b.toRat-a.toRat := by
    have hacR := (Fraction.le_iff_toRat a c).mp hac
    have hcbR := (Fraction.lt_iff_toRat c b).mp hcb
    grind
  intro n m _ hnm
  let q : Rat := R.toRat / (2*(n : Rat)+2)
  let e : Rat := q / (2*(b.toRat-a.toRat)+1)
  have hn : 0≤(n : Rat) := Rat.natCast_nonneg
  have hden : 0<2*(n : Rat)+2 := by grind
  have hwden : 0<2*(b.toRat-a.toRat)+1 := by grind
  have hq : 0<q := by
    dsimp only [q]
    grind only [Rat.div_def,Rat.inv_pos,Rat.mul_pos]
  have he : 0<e := by
    dsimp only [e]
    grind only [Rat.div_def,Rat.inv_pos,Rat.mul_pos]
  have hqeq : q*(2*(n : Rat)+2)=R.toRat := Rat.div_mul_cancel (Rat.ne_of_gt hden)
  have heq : e*(2*(b.toRat-a.toRat)+1)=q := Rat.div_mul_cancel (Rat.ne_of_gt hwden)
  refine ⟨Fraction.ofRat e,(Fraction.positive_iff_toRat _).mpr
    (by simpa only [Fraction.toRat_ofRat] using he),fun eps heps hcut => ?_⟩
  have hcutR := (Fraction.le_iff_toRat _ _).mp hcut
  rw [Fraction.toRat_ofRat] at hcutR
  obtain ⟨delta,hdelta,hfine⟩ := fine_rectangles area g a b A hzero hf hA eps heps
  refine ⟨delta,hdelta,fun p hp => ?_⟩
  obtain ⟨henclose,hgap⟩ := hfine p hp
  let L := value p (lowerHeights g p eps)
  let U := value p (upperHeights g p eps)
  have hRU : R.toRat≤U.toRat := (Fraction.le_iff_toRat R U).mp
    ((area.magnitudes.embed_le R U).mp
      (area.magnitudes.order.le_trans hRA henclose.2.2.2.2.2))
  have hgapR : U.toRat-L.toRat < q := by
    have hb := (Fraction.le_iff_toRat _ _).mp hgap
    rw [Fraction.toRat_durationDifference,Fraction.toRat_mul,Fraction.toRat_add,
      Fraction.toRat_durationDifference] at hb
    have hscale := Rat.mul_le_mul_of_nonneg_right
      (show eps.toRat+eps.toRat≤e+e by grind) hwidth
    change U.toRat-L.toRat ≤ (eps.toRat+eps.toRat)*(b.toRat-a.toRat) at hb
    grind
  have hqn := Rat.mul_nonneg (Rat.le_of_lt hq) hn
  have hBL : Fraction.le R.half L := by
    apply (Fraction.le_iff_toRat _ _).mpr
    rw [Fraction.toRat_half]
    grind
  have hsmall : Fraction.lt (Fraction.mul (Fraction.ofInt (n : Int))
      (durationDifference L U)) R.half := by
    apply (Fraction.lt_iff_toRat _ _).mpr
    rw [Fraction.toRat_mul,Fraction.toRat_ofInt,Fraction.toRat_durationDifference,
      Fraction.toRat_half,Rat.intCast_natCast]
    have hscaled := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hgapR) hn
    grind
  exact ⟨henclose,MagnitudeContent.finite_ratios_of_enclosure area.magnitudes
    multiples n m hnm R.half L U hR hBL hsmall⟩

end NewtonLimitDynamics.Polygon.UniformRectangles
