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
  let eps := (factorDelta C q hC).half
  have heps : 0<eps.num := factorDelta_positive C q hC hq
  obtain ⟨delta,hdelta,hfine⟩ := fine_rectangles area g a b A hzero hf hA eps heps
  refine ⟨eps,delta,heps,hdelta,fun p hp => ?_⟩
  obtain ⟨henclose,hbound⟩ := hfine p hp
  have he : Fraction.equiv (Fraction.mul (Fraction.add eps eps) (durationDifference a b))
      (Fraction.mul eps C) := by
    simp only [C,Fraction.equiv,Fraction.mul,Fraction.add,Fraction.ofInt,
      Int.one_mul,Int.mul_one,Int.add_mul,Int.mul_add]
    simp only [show (2 : Int) = 1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  have hsmall := Fraction.magnitudes.lt_of_le_lt (Fraction.le_equiv_right hbound he)
    (factor_control C q eps hC (Int.le_of_lt heps)
      (Fraction.half_lt (factorDelta C q hC) (factorDelta_positive C q hC hq)))
  have hgap := area.magnitudes.order.lt_of_le_lt
    ((area.magnitudes.embed_le _ _).mpr (Fraction.magnitudes.lt_implies_le hsmall)) hj
  exact ⟨henclose,hgap,MagnitudeContent.enclosure_errors_lt area.magnitudes _ _ A d
    henclose.2.2.2.2 hgap⟩

end NewtonLimitDynamics.Polygon.UniformRectangles
