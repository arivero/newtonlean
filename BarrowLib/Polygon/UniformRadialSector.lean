import BarrowLib.Polygon.RadialSector
import BarrowLib.Polygon.UniformRectangles

/-! Radial-sector exhaustion for a positive, bounded, uniformly continuous
rational slope chart, without a monotonicity premise (newtonlean issue 3).
In the coordinates `ray r θ = (r, rθ)` the chart `g` gives the positive first
coordinate of the curve at slope `θ`. On every ordered partition fine enough
for the explicit uniform modulus, the caps of scale `g(θᵢ) ∓ ε` are actual
finite triangle unions that enclose both the filled sector and its chord fan;
their area gap is exactly `Σ Δθᵢ · 2ε g(θᵢ)` and at most `2Mε(b-a)`. Endpoint
scales may rise or fall and nodes may repeat. Under the existing partial area
rules any assigned sector area lies within that gap of the chord-fan area, and
under the subtraction rule the collar between the caps has the gap as its area
and bounds any assigned area of the symmetric difference.

The statements and elementary finite proofs are project derivations of the
textbook lower/upper-sum squeeze, written for the radial area element
`½ g² dθ`; no exact external theorem or historical priority is claimed, and
no Newton text is quoted. This is the radial counterpart of
`UniformRectangles`. Uniform continuity and the bounds `m ≤ g ≤ M` are
explicit premises, not attributed to Newton. Curved-area existence, a uniform
mechanical chart and its Proposition I clients are not supplied here. -/

namespace NewtonLimitDynamics.Polygon.UniformRadialSector
open NewtonLimitDynamics TimeSubdivision ConvexCover SupportingTangents
open MonotoneRectangles HarmonicTimeComparison PolygonFanArea
open RadialSector


/-- Caps enclosure from pointwise bounds on one slope interval. -/
theorem caps_enclosure_bounds (g : Fraction → Fraction) (a b R S : Fraction)
    (hab : Fraction.le a b) (hR : 0 ≤ R.num)
    (hpos : ∀ t, Fraction.le a t → Fraction.le t b → 0 < (g t).num)
    (hlow : ∀ t, Fraction.le a t → Fraction.le t b → Fraction.le R (g t))
    (hup : ∀ t, Fraction.le a t → Fraction.le t b → Fraction.le (g t) S) :
    (∀ x, SectorFan.Triangle (ray R a) (ray R b) x → sector g a b x) ∧
    (∀ x, sector g a b x → SectorFan.Triangle (ray S a) (ray S b) x) := by
  constructor
  · intro x hx
    obtain ⟨r,u,hr,hu,he⟩ := (triangle_radial _ _ _).mp hx
    let t := affine u a b
    have ht := affine_between u a b hu hab
    obtain ⟨w,hw,heq⟩ := scale_to_cap r R (g t) hr hR (hpos t ht.1 ht.2) (hlow t ht.1 ht.2)
    refine ⟨t,ht.1,ht.2,w,hw,?_⟩
    exact pointEquiv_trans he (pointEquiv_trans (pointScale_congr r (ray_lerp u R a b))
      (scaled_ray_congr t (Fraction.equiv_symm heq)))
  · rintro x ⟨t,hat,htb,r,hr,he⟩
    have hS := positive_of_le _ _ (hpos t hat htb) (hup t hat htb)
    obtain ⟨w,hw,heq⟩ := scale_to_cap r (g t) S hr
      (Int.le_of_lt (hpos t hat htb)) hS (hup t hat htb)
    obtain ⟨u,hu,heu⟩ := interval_parameter a b t hat htb
    apply (triangle_radial _ _ _).mpr
    refine ⟨w,u,hw,hu,?_⟩
    have hline := pointEquiv_trans (ray_lerp u S a b) (ray_congr_slope S heu)
    exact pointEquiv_trans he (pointEquiv_trans (scaled_ray_congr t (Fraction.equiv_symm heq))
      (pointEquiv_symm (pointScale_congr w hline)))

/-- Chord enclosure for either ordering of the endpoint scales `P`, `Q`. -/
theorem cap_chord_enclosure_bounds (R P Q S a b : Fraction) (hR : 0 ≤ R.num)
    (hP : 0 < P.num) (hQ : 0 < Q.num)
    (hRP : Fraction.le R P) (hRQ : Fraction.le R Q)
    (hPS : Fraction.le P S) (hQS : Fraction.le Q S) :
    (∀ x, SectorFan.Triangle (ray R a) (ray R b) x →
      SectorFan.Triangle (ray P a) (ray Q b) x) ∧
    (∀ x, SectorFan.Triangle (ray P a) (ray Q b) x →
      SectorFan.Triangle (ray S a) (ray S b) x) := by
  have hS := positive_of_le P S hP hPS
  obtain ⟨u,hu,he⟩ := radial_vertex R P a hR hP hRP
  obtain ⟨v,hv,hf⟩ := radial_vertex R Q b hR hQ hRQ
  obtain ⟨u',hu',he'⟩ := radial_vertex P S a (Int.le_of_lt hP) hS hPS
  obtain ⟨v',hv',hf'⟩ := radial_vertex Q S b (Int.le_of_lt hQ) hS hQS
  exact ⟨triangle_inclusion (triangle_congr_point he (triangle_scale_left _ _ u hu))
      (triangle_congr_point hf (triangle_scale_right _ _ v hv)),
    triangle_inclusion (triangle_congr_point he' (triangle_scale_left _ _ u' hu'))
      (triangle_congr_point hf' (triangle_scale_right _ _ v' hv'))⟩

/-- Finite enclosure for arbitrary cell scales `lo`, `hi` that bound the chart on each cell. -/
theorem strips_enclosure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (lo hi : Nat → Fraction) (hlo : ∀ i, i < p.count → 0 ≤ (lo i).num)
    (hpos : ∀ t, Fraction.le a t → Fraction.le t b → 0 < (g t).num)
    (hcell : ∀ i, i < p.count → ∀ t, Fraction.le (p.nodes i) t →
      Fraction.le t (p.nodes (i+1)) → Fraction.le (lo i) (g t) ∧ Fraction.le (g t) (hi i)) :
    (∀ x, strips p lo p.count x → sector g a b x) ∧
    (∀ x, sector g a b x → strips p hi p.count x) ∧
    (∀ x, strips p lo p.count x → chordFigure g p x) ∧
    (∀ x, chordFigure g p x → strips p hi p.count x) := by
  have hin (i : Nat) (hi' : i < p.count) (t : Fraction) (hl : Fraction.le (p.nodes i) t)
      (hr : Fraction.le t (p.nodes (i+1))) : Fraction.le a t ∧ Fraction.le t b :=
    ⟨Fraction.magnitudes.le_trans (node_bounds p i (by omega)).1 hl,
      Fraction.magnitudes.le_trans hr (node_bounds p (i+1) (by omega)).2⟩
  have hcaps (i : Nat) (hi' : i < p.count) := caps_enclosure_bounds g (p.nodes i) (p.nodes (i+1))
    (lo i) (hi i) (p.ordered i hi') (hlo i hi')
    (fun t hl hr => hpos t (hin i hi' t hl hr).1 (hin i hi' t hl hr).2)
    (fun t hl hr => (hcell i hi' t hl hr).1) (fun t hl hr => (hcell i hi' t hl hr).2)
  have hnode (i : Nat) (hi' : i ≤ p.count) : 0 < (g (p.nodes i)).num :=
    hpos _ (node_bounds p i hi').1 (node_bounds p i hi').2
  have hchord (i : Nat) (hi' : i < p.count) := cap_chord_enclosure_bounds (lo i)
    (g (p.nodes i)) (g (p.nodes (i+1))) (hi i) (p.nodes i) (p.nodes (i+1)) (hlo i hi')
    (hnode i (by omega)) (hnode (i+1) (by omega))
    (hcell i hi' _ (Fraction.magnitudes.le_refl _) (p.ordered i hi')).1
    (hcell i hi' _ (p.ordered i hi') (Fraction.magnitudes.le_refl _)).1
    (hcell i hi' _ (Fraction.magnitudes.le_refl _) (p.ordered i hi')).2
    (hcell i hi' _ (p.ordered i hi') (Fraction.magnitudes.le_refl _)).2
  refine ⟨?_,?_,?_,?_⟩
  · rintro x ⟨i,hi',hx⟩
    obtain ⟨t,hat,htb,r,hr,he⟩ := (hcaps i hi').1 x hx
    exact ⟨t,(hin i hi' t hat htb).1,(hin i hi' t hat htb).2,r,hr,he⟩
  · rintro x ⟨t,hat,htb,r,hr,he⟩
    obtain ⟨i,hi',hl,hu⟩ := partition_cover p t hat htb
    exact ⟨i,hi',(hcaps i hi').2 x ⟨t,hl,hu,r,hr,he⟩⟩
  · rintro x ⟨i,hi',hx⟩
    exact ⟨i,hi',(hchord i hi').1 x hx⟩
  · rintro x ⟨i,hi',hx⟩
    exact ⟨i,hi',(hchord i hi').2 x hx⟩

/-- The chord fan has its determinant area from pointwise positivity alone. -/
theorem chord_area_positive (area : SectorFan.AreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b)
    (hpos : ∀ t, Fraction.le a t → Fraction.le t b → 0 < (g t).num) :
    area.HasArea (chordFigure g p) (chordArea g p) := by
  have hnode (i : Nat) (hi' : i ≤ p.count) : 0 < (g (p.nodes i)).num :=
    hpos _ (node_bounds p i hi').1 (node_bounds p i hi').2
  exact SectorFan.region_area area _ _ (fun i hi => hnode i hi)
    (fun i hi => ray_orientation _ _ _ _ (Int.le_of_lt (hnode i (by omega)))
      (Int.le_of_lt (hnode (i+1) (by omega))) (p.ordered i hi))

/-- Gap of two strip sums from a common bound on the half-square differences. -/
theorem strip_gap_bound {a b : Fraction} (p : Partition a b) (lo hi : Nat → Fraction)
    (E : Fraction)
    (hb : ∀ i, i < p.count → Fraction.le (durationDifference
      (Fraction.mul (lo i) (lo i)).half (Fraction.mul (hi i) (hi i)).half) E) :
    Fraction.le (durationDifference (stripSum p lo p.count) (stripSum p hi p.count))
      (Fraction.mul E (durationDifference a b)) := by
  have he : Fraction.equiv (durationDifference (stripSum p lo p.count) (stripSum p hi p.count))
      (sum (fun i => Fraction.mul (width p i) (durationDifference
        (Fraction.mul (lo i) (lo i)).half (Fraction.mul (hi i) (hi i)).half)) p.count) := by
    apply Fraction.equiv_trans (sum_difference _ _ p.count)
    apply sum_congr
    intro i
    simp only [sub,neg,durationDifference,HarmonicStability.negF,Fraction.equiv,
      Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf
  have hsum := sum_mono _ (fun i => Fraction.mul E (width p i)) p.count (fun i hi' =>
    Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative_left (hb i hi')
      (width p i) ((difference_nonnegative_iff _ _).mpr (p.ordered i hi')))
      (Fraction.mul_comm _ _))
  exact Fraction.le_equiv_left he (Fraction.le_equiv_right hsum
    (Fraction.equiv_trans (sum_mul (width p) E p.count)
      (Fraction.mul_equiv_left E (Fraction.equiv_trans (sum_telescope p.nodes p.count)
        (difference_congr p.first p.last)))))

/-- Lower and upper cap scales `g(θ_i) ∓ ε`. -/
def lowerScales {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (eps : Fraction) :
    Nat → Fraction := fun i => durationDifference eps (g (p.nodes i))
def upperScales {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (eps : Fraction) :
    Nat → Fraction := fun i => Fraction.add (g (p.nodes i)) eps

/-- The half-square difference of the two cap scales is `2 ε g`. -/
theorem scale_gap (G eps : Fraction) :
    Fraction.equiv (durationDifference
      (Fraction.mul (durationDifference eps G) (durationDifference eps G)).half
      (Fraction.mul (Fraction.add G eps) (Fraction.add G eps)).half)
      (Fraction.mul (Fraction.add eps eps) G) := by
  apply (Fraction.equiv_iff_toRat _ _).mpr
  simp only [Fraction.toRat_durationDifference, Fraction.toRat_half, Fraction.toRat_mul,
    Fraction.toRat_add]
  grind

/-- Exact gap identity: `A(U) - A(L) = Σ Δθ_i · 2 ε g_i`. -/
theorem caps_gap_identity {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (eps : Fraction) :
    Fraction.equiv (durationDifference (stripSum p (lowerScales g p eps) p.count)
        (stripSum p (upperScales g p eps) p.count))
      (sum (fun i => Fraction.mul (width p i)
        (Fraction.mul (Fraction.add eps eps) (g (p.nodes i)))) p.count) := by
  apply Fraction.equiv_trans (sum_difference _ _ p.count)
  apply sum_congr
  intro i
  apply (Fraction.equiv_iff_toRat _ _).mpr
  simp only [sub, neg, lowerScales, upperScales, Fraction.toRat_add, Fraction.toRat_mul,
    Fraction.toRat_half]
  have hneg (x : Fraction) : (⟨-x.num, x.den, x.den_pos⟩ : Fraction).toRat = -x.toRat :=
    Fraction.toRat_negF x
  simp only [hneg, Fraction.toRat_mul, Fraction.toRat_half, Fraction.toRat_durationDifference]
  grind

/-- The gap is at most `2 M ε (b - a)` when the node scales are nonnegative and at most `M`. -/
theorem caps_gap_bound {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (eps M : Fraction) (heps : 0 ≤ eps.num)
    (hM : ∀ i, i < p.count → Fraction.le (g (p.nodes i)) M) :
    Fraction.le (durationDifference (stripSum p (lowerScales g p eps) p.count)
        (stripSum p (upperScales g p eps) p.count))
      (Fraction.mul (Fraction.mul (Fraction.add eps eps) M) (durationDifference a b)) := by
  apply strip_gap_bound p _ _ _
  intro i hi
  exact Fraction.le_equiv_left (scale_gap (g (p.nodes i)) eps)
    (Fraction.mul_le_mul_nonnegative_left (hM i hi) (Fraction.add eps eps)
      (Fraction.nonnegative_add _ _ heps heps))

/-- Uniform continuity and a fine partition give the cell bounds `g_i - ε ≤ g ≤ g_i + ε`. -/
theorem fine_cell_bounds (g : Fraction → Fraction) (a b : Fraction)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ delta : Fraction, 0 < delta.num ∧ ∀ p : Partition a b, Fraction.le (maxWidth p) delta →
      ∀ i, i < p.count → ∀ t, Fraction.le (p.nodes i) t → Fraction.le t (p.nodes (i+1)) →
        Fraction.le (lowerScales g p eps i) (g t) ∧ Fraction.le (g t) (upperScales g p eps i) := by
  obtain ⟨delta,hdelta,hfdelta⟩ := hf eps heps
  refine ⟨delta,hdelta,fun p hp i hi t hl hr => ?_⟩
  have ht : Fraction.le a t ∧ Fraction.le t b :=
    ⟨Fraction.magnitudes.le_trans (node_bounds p i (by omega)).1 hl,
    Fraction.magnitudes.le_trans hr (node_bounds p (i+1) (by omega)).2⟩
  have hdist := Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right (difference_interval_gaps _ _ _ hl hr).1
      (Fraction.abs_of_nonnegative _ ((difference_nonnegative_iff _ _).mpr (p.ordered i hi))))
    (Fraction.magnitudes.le_trans ((maxWidth_bounds p).1 i hi) hp)
  have hc := hfdelta (p.nodes i) t (node_bounds p i (by omega)).1
    (node_bounds p i (by omega)).2 ht.1 ht.2 hdist
  have hy : Fraction.le (durationDifference (g t) (g (p.nodes i))).abs
      (FiniteEstimates.pointDistance (p.nodes i,g (p.nodes i)) (t,g t)) :=
    Fraction.le_equiv_right
      (Fraction.le_add_nonnegative _ (durationDifference t (p.nodes i)).abs
        (Fraction.abs_num_nonnegative _)) (Fraction.add_comm _ _)
  have habs := Fraction.magnitudes.lt_of_le_lt hy hc
  have hR := (Fraction.lt_iff_toRat _ _).mp habs
  rw [Fraction.toRat_abs, Fraction.toRat_durationDifference] at hR
  have hlt : -(eps.toRat) < (g (p.nodes i)).toRat - (g t).toRat ∧
      (g (p.nodes i)).toRat - (g t).toRat < eps.toRat := by
    simp only [Rat.abs] at hR
    split at hR <;> grind
  constructor
  · apply (Fraction.le_iff_toRat _ _).mpr
    simp only [lowerScales, Fraction.toRat_durationDifference]
    grind
  · apply (Fraction.le_iff_toRat _ _).mpr
    simp only [upperScales, Fraction.toRat_add]
    grind

/-- The cap figures of one partition. -/
def lowerCaps {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (eps : Fraction) :
    Point → Prop := strips p (lowerScales g p eps) p.count
def upperCaps {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (eps : Fraction) :
    Point → Prop := strips p (upperScales g p eps) p.count
def capsGap {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (eps : Fraction) :
    Fraction := durationDifference (stripSum p (lowerScales g p eps) p.count)
      (stripSum p (upperScales g p eps) p.count)

/-- Conclusions for one partition: the four inclusions, the three finite areas and the gap bound. -/
def CapsEnclose (area : SectorFan.AreaRules) (g : Fraction → Fraction) (a b : Fraction)
    (p : Partition a b) (eps M : Fraction) : Prop :=
  (∀ x, lowerCaps g p eps x → sector g a b x) ∧
  (∀ x, sector g a b x → upperCaps g p eps x) ∧
  (∀ x, lowerCaps g p eps x → chordFigure g p x) ∧
  (∀ x, chordFigure g p x → upperCaps g p eps x) ∧
  area.HasArea (lowerCaps g p eps) (stripSum p (lowerScales g p eps) p.count) ∧
  area.HasArea (upperCaps g p eps) (stripSum p (upperScales g p eps) p.count) ∧
  area.HasArea (chordFigure g p) (chordArea g p) ∧
  Fraction.le (capsGap g p eps)
    (Fraction.mul (Fraction.mul (Fraction.add eps eps) M) (durationDifference a b))

/-- Uniform continuity gives actual lower and upper caps on every sufficiently fine partition,
without monotonicity of the chart. -/
theorem fine_caps (area : SectorFan.AreaRules) (g : Fraction → Fraction) (a b m M : Fraction)
    (hm : 0 < m.num)
    (hbounds : ∀ t, Fraction.le a t → Fraction.le t b → Fraction.le m (g t) ∧ Fraction.le (g t) M)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (eps : Fraction) (heps : 0 < eps.num) (hem : Fraction.le eps m) :
    ∃ delta : Fraction, 0 < delta.num ∧ ∀ p : Partition a b, Fraction.le (maxWidth p) delta →
      CapsEnclose area g a b p eps M := by
  obtain ⟨delta,hdelta,hfine⟩ := fine_cell_bounds g a b hf eps heps
  refine ⟨delta,hdelta,fun p hp => ?_⟩
  have hpos (t : Fraction) (hat : Fraction.le a t) (htb : Fraction.le t b) : 0 < (g t).num :=
    positive_of_le _ _ hm (hbounds t hat htb).1
  have hnode (i : Nat) (hi : i ≤ p.count) := hbounds _ (node_bounds p i hi).1 (node_bounds p i hi).2
  have hlo (i : Nat) (hi : i < p.count) : 0 ≤ (lowerScales g p eps i).num :=
    (difference_nonnegative_iff _ _).mpr (Fraction.magnitudes.le_trans hem (hnode i (by omega)).1)
  have hhi (i : Nat) (hi : i < p.count) : 0 ≤ (upperScales g p eps i).num :=
    Fraction.nonnegative_add _ _ (Int.le_of_lt (hpos _ (node_bounds p i (by omega)).1
      (node_bounds p i (by omega)).2)) (Int.le_of_lt heps)
  have hs := strips_enclosure g p (lowerScales g p eps) (upperScales g p eps) hlo hpos
    (hfine p hp)
  exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    strips_area area p _ hlo p.count (Nat.le_refl _),
    strips_area area p _ hhi p.count (Nat.le_refl _),
    chord_area_positive area g p hpos,
    caps_gap_bound g p eps M (Int.le_of_lt heps) (fun i hi => (hnode i (by omega)).2)⟩

/-- Any assigned sector area differs from the chord-fan area by at most the cap gap. -/
theorem chord_error_caps (area : SectorFan.AreaRules) {a b : Fraction} (g : Fraction → Fraction)
    (p : Partition a b) (eps M A : Fraction) (h : CapsEnclose area g a b p eps M)
    (hA : area.HasArea (sector g a b) A) :
    Fraction.le (durationDifference A (chordArea g p)).abs (capsGap g p eps) := by
  obtain ⟨hLS,hSU,hLC,hCU,hL,hU,hC,_⟩ := h
  exact interval_difference_bound _ _ _ _ (area.monotone _ _ _ _ hLS hL hA)
    (area.monotone _ _ _ _ hSU hA hU) (area.monotone _ _ _ _ hLC hL hC)
    (area.monotone _ _ _ _ hCU hC hU)

/-- The collar between the two cap figures. -/
def capsCollar {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (eps : Fraction)
    (x : Point) : Prop := upperCaps g p eps x ∧ ¬ lowerCaps g p eps x

/-- The actual symmetric difference of sector and chord fan lies in the collar; with the
subtraction rule the collar has the gap as area and bounds any assigned between-area. -/
theorem between_caps (area : DifferenceAreaRules) {a b : Fraction} (g : Fraction → Fraction)
    (p : Partition a b) (eps M : Fraction)
    (h : CapsEnclose area.toSectorAreaRules g a b p eps M) :
    (∀ x, between g p x → capsCollar g p eps x) ∧
    area.HasArea (capsCollar g p eps) (capsGap g p eps) ∧
    ∀ B, area.HasArea (between g p) B → 0 ≤ B.num ∧ Fraction.le B (capsGap g p eps) := by
  obtain ⟨hLS,hSU,hLC,hCU,hL,hU,_,_⟩ := h
  have hsub : ∀ x, between g p x → capsCollar g p eps x := by
    rintro x (⟨hx,hn⟩ | ⟨hx,hn⟩)
    · exact ⟨hSU x hx,fun hl => hn (hLC x hl)⟩
    · exact ⟨hCU x hx,fun hl => hn (hLS x hl)⟩
  have hcol : area.HasArea (capsCollar g p eps) (capsGap g p eps) :=
    area.subtract _ _ _ _ (fun x hx => hSU x (hLS x hx)) hL hU
  exact ⟨hsub,hcol,fun B hB => ⟨assigned_area_nonnegative area.toSectorAreaRules _ B hB,
    area.monotone _ _ _ _ hsub hB hcol⟩⟩

/-- Exhaustion: every positive tolerance is met by every sufficiently fine partition. -/
theorem caps_exhaust (area : SectorFan.AreaRules) (g : Fraction → Fraction) (a b m M : Fraction)
    (hab : Fraction.le a b) (hm : 0 < m.num)
    (hbounds : ∀ t, Fraction.le a t → Fraction.le t b → Fraction.le m (g t) ∧ Fraction.le (g t) M)
    (hf : RationalBoundary.UniformOn (fun t => (t,g t)) a b)
    (eta : Fraction) (heta : 0 < eta.num) :
    ∃ eps delta : Fraction, 0 < eps.num ∧ Fraction.le eps m ∧ 0 < delta.num ∧
      ∀ p : Partition a b, Fraction.le (maxWidth p) delta →
        CapsEnclose area g a b p eps M ∧ Fraction.lt (capsGap g p eps) eta := by
  have hmR := (Fraction.positive_iff_toRat m).mp hm
  have hetaR := (Fraction.positive_iff_toRat eta).mp heta
  have habR := (Fraction.le_iff_toRat a b).mp hab
  have hmM := (Fraction.le_iff_toRat _ _).mp
    (Fraction.magnitudes.le_trans (hbounds a (Fraction.magnitudes.le_refl _) hab).1
      (hbounds a (Fraction.magnitudes.le_refl _) hab).2)
  let K : Rat := (M.toRat + M.toRat) * (b.toRat - a.toRat)
  have hK : 0 ≤ K := Rat.mul_nonneg (by grind) (by grind)
  let c : Rat := eta.toRat / (K + 1)
  have hc : 0 < c := by
    have hK1 : 0 < K + 1 := by grind
    show 0 < eta.toRat / (K + 1)
    rw [Rat.div_def]
    exact Rat.mul_pos hetaR (Rat.inv_pos.mpr hK1)
  have hcK : c * K + c = eta.toRat := by
    have : c = eta.toRat / (K + 1) := rfl
    grind
  let eps := Fraction.ofRat (min m.toRat c)
  have hepsR : eps.toRat = min m.toRat c := Fraction.toRat_ofRat _
  have heps : 0 < eps.num := (Fraction.positive_iff_toRat eps).mpr (by rw [hepsR]; grind)
  have hem : Fraction.le eps m := (Fraction.le_iff_toRat _ _).mpr (by rw [hepsR]; grind)
  obtain ⟨delta,hdelta,hfine⟩ := fine_caps area g a b m M hm hbounds hf eps heps hem
  refine ⟨eps,delta,heps,hem,hdelta,fun p hp => ⟨hfine p hp,?_⟩⟩
  apply Fraction.magnitudes.lt_of_le_lt (hfine p hp).2.2.2.2.2.2.2
  apply (Fraction.lt_iff_toRat _ _).mpr
  simp only [Fraction.toRat_mul, Fraction.toRat_add, Fraction.toRat_durationDifference]
  have hle : eps.toRat * K ≤ c * K := Rat.mul_le_mul_of_nonneg_right (by rw [hepsR]; grind) hK
  have hKdef : K = (M.toRat + M.toRat) * (b.toRat - a.toRat) := rfl
  grind

end NewtonLimitDynamics.Polygon.UniformRadialSector
