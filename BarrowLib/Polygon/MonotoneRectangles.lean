import BarrowLib.Polygon.PolygonFanArea
import BarrowLib.Common.RationalTolerance

/-! Explicit lower/upper rectangle sets around a given rational monotone
graph. Their inclusion is derived from graph monotonicity and finite ordered
partition coverage. Rectangle side-product sums have a derived maximum-width
gap and exhaustion. Sums are finite rectangle-area arithmetic: identification
with ordinary union content or a completed curvilinear area is separate. -/

namespace NewtonLimitDynamics.Polygon.MonotoneRectangles
open NewtonLimitDynamics TimeSubdivision
open HarmonicTimeComparison HarmonicTimeRealization PolygonFanArea

structure Partition (a b : Fraction) where
  count : Nat
  positive_count : 0<count
  nodes : Nat → Fraction
  first : Fraction.equiv (nodes 0) a
  last : Fraction.equiv (nodes count) b
  ordered : ∀ i, i<count → Fraction.le (nodes i) (nodes (i+1))

def MonotoneOn (g : Fraction → Fraction) (a b : Fraction) : Prop :=
  ∀ x y, Fraction.le a x → Fraction.le x y → Fraction.le y b → Fraction.le (g x) (g y)

private theorem node_order {a b : Fraction} (p : Partition a b) (j : Nat) :
    ∀ i, i≤j → j≤p.count → Fraction.le (p.nodes i) (p.nodes j) := by
  induction j with
  | zero =>
    intro i hi _
    have he : i=0 := by omega
    subst i
    exact Fraction.magnitudes.le_refl _
  | succ j ih =>
    intro i hij hj
    by_cases hi : i≤j
    · exact Fraction.magnitudes.le_trans (ih i hi (by omega)) (p.ordered j (by omega))
    · have he : i=j+1 := by omega
      subst i
      exact Fraction.magnitudes.le_refl _

theorem node_bounds {a b : Fraction} (p : Partition a b) (i : Nat) (hi : i≤p.count) :
    Fraction.le a (p.nodes i) ∧ Fraction.le (p.nodes i) b :=
  ⟨Fraction.le_equiv_left (Fraction.equiv_symm p.first) (node_order p i 0 (by omega) hi),
    Fraction.le_equiv_right (node_order p p.count i hi (Nat.le_refl _)) p.last⟩

/-- Coverage, including repeated nodes and the final endpoint, is a theorem
of the finite ordered partition rather than an enclosure field. -/
theorem partition_cover {a b : Fraction} (p : Partition a b) (x : Fraction)
    (ha : Fraction.le a x) (hb : Fraction.le x b) :
    ∃ i, i<p.count ∧ Fraction.le (p.nodes i) x ∧ Fraction.le x (p.nodes (i+1)) := by
  have cover (nodes : Nat → Fraction) (n : Nat) (hn : 0<n)
      (h0 : Fraction.le (nodes 0) x) (h1 : Fraction.le x (nodes n)) :
      ∃ i, i<n ∧ Fraction.le (nodes i) x ∧ Fraction.le x (nodes (i+1)) := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases he : n=0
      · subst n; exact ⟨0,by decide,h0,h1⟩
      · by_cases hx : Fraction.le x (nodes n)
        · obtain ⟨i,hi,hl,hr⟩ := ih (by omega) hx
          exact ⟨i,by omega,hl,hr⟩
        · exact ⟨n,by omega,by unfold Fraction.le at *; omega,h1⟩
  exact cover p.nodes p.count p.positive_count
    (Fraction.le_equiv_left p.first ha) (Fraction.le_equiv_right hb (Fraction.equiv_symm p.last))

def rectangle (left right height : Fraction) (x : Point) : Prop :=
  Fraction.le left x.1 ∧ Fraction.le x.1 right ∧ 0≤x.2.num ∧ Fraction.le x.2 height

def figure (g : Fraction → Fraction) (a b : Fraction) (x : Point) : Prop :=
  Fraction.le a x.1 ∧ Fraction.le x.1 b ∧ 0≤x.2.num ∧ Fraction.le x.2 (g x.1)

def lowerFigure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (x : Point) : Prop :=
  ∃ i, i<p.count ∧ rectangle (p.nodes i) (p.nodes (i+1)) (g (p.nodes i)) x

def upperFigure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (x : Point) : Prop :=
  ∃ i, i<p.count ∧ rectangle (p.nodes i) (p.nodes (i+1)) (g (p.nodes (i+1))) x

/-- The actual rational rectangle sets enclose the given graph region. -/
theorem figure_enclosure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) :
    (∀ x, lowerFigure g p x → figure g a b x) ∧
      (∀ x, figure g a b x → upperFigure g p x) := by
  constructor
  · intro x hx
    obtain ⟨i,hi,hl,hr,hy0,hy⟩ := hx
    have hleft := (node_bounds p i (by omega)).1
    have hright := (node_bounds p (i+1) (by omega)).2
    have hxb := Fraction.magnitudes.le_trans hr hright
    exact ⟨Fraction.magnitudes.le_trans hleft hl,hxb,hy0,
      Fraction.magnitudes.le_trans hy (hg _ _ hleft hl hxb)⟩
  · intro x hx
    obtain ⟨ha,hb,hy0,hy⟩ := hx
    obtain ⟨i,hi,hl,hr⟩ := partition_cover p x.1 ha hb
    exact ⟨i,hi,hl,hr,hy0,Fraction.magnitudes.le_trans hy
      (hg _ _ ha hr (node_bounds p (i+1) (by omega)).2)⟩

def width {a b : Fraction} (p : Partition a b) (i : Nat) : Fraction :=
  durationDifference (p.nodes i) (p.nodes (i+1))

private noncomputable def prefixMax (f : Nat → Fraction) : Nat → Fraction
  | 0 => f 0
  | n+1 => by
      classical
      exact if Fraction.le (prefixMax f n) (f (n+1)) then f (n+1) else prefixMax f n

private theorem prefixMax_bounds (f : Nat → Fraction) (n : Nat) :
    (∀ i, i≤n → Fraction.le (f i) (prefixMax f n)) ∧
      (∀ M, (∀ i, i≤n → Fraction.le (f i) M) → Fraction.le (prefixMax f n) M) := by
  classical
  induction n with
  | zero =>
    constructor
    · intro i hi
      have he : i=0 := by omega
      simpa only [he,prefixMax] using Fraction.magnitudes.le_refl (f 0)
    · intro M hM; exact hM 0 (Nat.le_refl _)
  | succ n ih =>
    simp only [prefixMax]
    split
    · rename_i h
      constructor
      · intro i hi
        by_cases he : i≤n
        · exact Fraction.magnitudes.le_trans (ih.1 i he) h
        · have he' : i=n+1 := by omega
          subst i
          exact Fraction.magnitudes.le_refl _
      · intro M hM; exact hM (n+1) (Nat.le_refl _)
    · rename_i h
      have hr : Fraction.le (f (n+1)) (prefixMax f n) := by unfold Fraction.le at *; omega
      constructor
      · intro i hi
        by_cases he : i≤n
        · exact ih.1 i he
        · have he' : i=n+1 := by omega
          subst i
          exact hr
      · intro M hM; exact ih.2 M (fun i hi => hM i (by omega))

/-- The largest actual cell width, constructed from the finite partition. -/
noncomputable def maxWidth {a b : Fraction} (p : Partition a b) : Fraction :=
  prefixMax (width p) (p.count-1)

theorem maxWidth_bounds {a b : Fraction} (p : Partition a b) :
    (∀ i, i<p.count → Fraction.le (width p i) (maxWidth p)) ∧
      (∀ M, (∀ i, i<p.count → Fraction.le (width p i) M) → Fraction.le (maxWidth p) M) := by
  have hs := prefixMax_bounds (width p) (p.count-1)
  exact ⟨fun i hi => hs.1 i (by omega),fun M hM => hs.2 M (fun i hi => hM i (by
    have := p.positive_count; omega))⟩

def lowerSum {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) : Fraction :=
  sum (fun i => Fraction.mul (width p i) (g (p.nodes i))) p.count

def upperSum {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) : Fraction :=
  sum (fun i => Fraction.mul (width p i) (g (p.nodes (i+1)))) p.count

def gap {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) : Fraction :=
  durationDifference (lowerSum g p) (upperSum g p)

theorem gap_identity {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) :
    Fraction.equiv (gap g p)
      (sum (fun i => Fraction.mul (width p i)
        (durationDifference (g (p.nodes i)) (g (p.nodes (i+1))))) p.count) := by
  apply Fraction.equiv_trans (sum_difference _ _ p.count)
  apply sum_congr
  intro i
  simp only [sub,neg,width,durationDifference,HarmonicStability.negF,Fraction.equiv,
    Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
  ac_nf

private theorem graph_congr {a b : Fraction} (g : Fraction → Fraction) (hg : MonotoneOn g a b)
    (x y : Fraction) (hx : Fraction.le a x ∧ Fraction.le x b)
    (hy : Fraction.le a y ∧ Fraction.le y b) (he : Fraction.equiv x y) :
    Fraction.equiv (g x) (g y) :=
  (Fraction.equiv_iff_mutual_le _ _).mpr
    ⟨hg x y hx.1 (Fraction.le_of_equiv he) hy.2,
      hg y x hy.1 (Fraction.le_of_equiv (Fraction.equiv_symm he)) hx.2⟩

private theorem height_sum {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) :
    Fraction.equiv (sum (fun i => durationDifference (g (p.nodes i)) (g (p.nodes (i+1)))) p.count)
      (durationDifference (g a) (g b)) := by
  have hab : Fraction.le a b := Fraction.magnitudes.le_trans (node_bounds p 0 (by omega)).1
    (node_bounds p 0 (by omega)).2
  have h0 := graph_congr g hg (p.nodes 0) a (node_bounds p 0 (by omega))
    ⟨Fraction.magnitudes.le_refl _,hab⟩ p.first
  have hn := graph_congr g hg (p.nodes p.count) b (node_bounds p p.count (Nat.le_refl _))
    ⟨hab,Fraction.magnitudes.le_refl _⟩ p.last
  exact Fraction.equiv_trans (sum_telescope (fun i => g (p.nodes i)) p.count)
    (difference_congr h0 hn)

theorem sums_nonnegative {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0≤(g a).num) :
    0≤(lowerSum g p).num ∧ 0≤(upperSum g p).num := by
  have hn (i : Nat) (hi : i≤p.count) : 0≤(g (p.nodes i)).num :=
    Fraction.nonnegative_of_le hbase (hg _ _ (Fraction.magnitudes.le_refl _)
      (node_bounds p i hi).1 (node_bounds p i hi).2)
  have hw (i : Nat) (hi : i<p.count) : 0≤(width p i).num :=
    (difference_nonnegative_iff _ _).mpr (p.ordered i hi)
  exact ⟨sum_nonnegative _ p.count (fun i hi => Fraction.nonnegative_mul _ _ (hw i hi) (hn i (by omega))),
    sum_nonnegative _ p.count (fun i hi => Fraction.nonnegative_mul _ _ (hw i hi) (hn (i+1) (by omega)))⟩

/-- Equal widths make the actual difference of the finite rectangle sums
exactly one width times the figure's total height (Lemma II's identity). -/
theorem gap_equal_width {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (M : Fraction)
    (hM : ∀ i, i<p.count → Fraction.equiv (width p i) M) :
    Fraction.equiv (gap g p) (Fraction.mul M (durationDifference (g a) (g b))) := by
  have hs : Fraction.equiv
      (sum (fun i => Fraction.mul (width p i)
        (durationDifference (g (p.nodes i)) (g (p.nodes (i+1))))) p.count)
      (sum (fun i => Fraction.mul M
        (durationDifference (g (p.nodes i)) (g (p.nodes (i+1))))) p.count) := by
    exact (Fraction.equiv_iff_mutual_le _ _).mpr
      ⟨sum_mono _ _ p.count (fun i hi => Fraction.le_of_equiv (Fraction.mul_equiv_right _ (hM i hi))),
        sum_mono _ _ p.count (fun i hi => Fraction.le_of_equiv
          (Fraction.equiv_symm (Fraction.mul_equiv_right _ (hM i hi))))⟩
  exact Fraction.equiv_trans (gap_identity g p) (Fraction.equiv_trans hs
    (Fraction.equiv_trans (sum_mul _ M p.count) (Fraction.mul_equiv_left M (height_sum g p hg))))

/-- The rational version of Newton's maximum-width times total-height gap.
The total height uses the fixed figure endpoints, including aliases. -/
theorem gap_bound {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (M : Fraction)
    (hM : ∀ i, i<p.count → Fraction.le (width p i) M) :
    0≤(gap g p).num ∧ Fraction.le (gap g p) (Fraction.mul M (durationDifference (g a) (g b))) := by
  have gh (i : Nat) (hi : i<p.count) : Fraction.le (g (p.nodes i)) (g (p.nodes (i+1))) :=
    hg _ _ (node_bounds p i (by omega)).1 (p.ordered i hi) (node_bounds p (i+1) (by omega)).2
  have hd (i : Nat) (hi : i<p.count) : 0≤(durationDifference (g (p.nodes i)) (g (p.nodes (i+1)))).num :=
    (difference_nonnegative_iff _ _).mpr (gh i hi)
  have hl : Fraction.le (lowerSum g p) (upperSum g p) :=
    sum_mono _ _ p.count (fun i hi => Fraction.mul_le_mul_nonnegative_left (gh i hi) (width p i)
      ((difference_nonnegative_iff _ _).mpr (p.ordered i hi)))
  refine ⟨(difference_nonnegative_iff _ _).mpr hl,?_⟩
  have hs := sum_mono _ _ p.count (fun i hi => Fraction.mul_le_mul_nonnegative (hM i hi)
    (durationDifference (g (p.nodes i)) (g (p.nodes (i+1)))) (hd i hi))
  have he := Fraction.equiv_trans (sum_mul _ M p.count)
    (Fraction.mul_equiv_left M (height_sum g p hg))
  exact Fraction.le_equiv_right (Fraction.le_equiv_left (gap_identity g p) hs)
    he

/-- Exhaustion is derived from maximum width shrinking. The gap is the
actual difference of the rectangle side-product sums, not a supplied budget. -/
theorem gaps_vanish {a b : Fraction} (g : Fraction → Fraction)
    (parts : Nat → Partition a b) (hg : MonotoneOn g a b)
    (hmesh : ∀ delta : Fraction, 0<delta.num → ∃ N : Nat, ∀ m, N≤m → Fraction.lt (maxWidth (parts m)) delta) :
    ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m → Fraction.lt (gap g (parts m)) eps := by
  have hab : Fraction.le a b := Fraction.magnitudes.le_trans
    (node_bounds (parts 0) 0 (by omega)).1 (node_bounds (parts 0) 0 (by omega)).2
  let H := durationDifference (g a) (g b)
  have hH : 0≤H.num := (difference_nonnegative_iff _ _).mpr
    (hg a b (Fraction.magnitudes.le_refl _) hab (Fraction.magnitudes.le_refl _))
  intro eps heps
  obtain ⟨N,hN⟩ := hmesh (factorDelta H eps hH) (factorDelta_positive H eps hH heps)
  refine ⟨N,?_⟩
  intro m hm
  have hn : 0≤(maxWidth (parts m)).num := Fraction.nonnegative_of_le
    ((difference_nonnegative_iff _ _).mpr ((parts m).ordered 0 (parts m).positive_count))
    ((maxWidth_bounds (parts m)).1 0 (parts m).positive_count)
  exact Fraction.magnitudes.lt_of_le_lt
    (gap_bound g (parts m) hg (maxWidth (parts m)) (maxWidth_bounds (parts m)).1).2
    (factor_control H eps (maxWidth (parts m)) hH hn (hN m hm))

end NewtonLimitDynamics.Polygon.MonotoneRectangles
