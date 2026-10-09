import BarrowLib.Polygon.PolygonFanArea
import BarrowLib.Polygon.RationalIntervals
import BarrowLib.Common.RationalTolerance

/-! Explicit lower/upper rectangle sets around a given rational monotone
graph. Their inclusion is derived from graph monotonicity and finite ordered
partition coverage. Rectangle side-product sums have a derived maximum-width
gap and exhaustion. Sums are finite rectangle-area arithmetic: identification
with ordinary union content or a completed curvilinear area is separate. -/

namespace NewtonLimitDynamics.Polygon.MonotoneRectangles
open NewtonLimitDynamics TimeSubdivision
open HarmonicTimeComparison HarmonicTimeRealization PolygonFanArea
open RationalIntervals

structure Partition (a b : Fraction) where
  count : Nat
  positive_count : 0<count
  nodes : Nat → Fraction
  first : Fraction.equiv (nodes 0) a
  last : Fraction.equiv (nodes count) b
  ordered : ∀ i, i<count → Fraction.le (nodes i) (nodes (i+1))

def MonotoneOn (g : Fraction → Fraction) (a b : Fraction) : Prop :=
  ∀ x y, Fraction.le a x → Fraction.le x y → Fraction.le y b → Fraction.le (g x) (g y)

theorem node_order {a b : Fraction} (p : Partition a b) (j : Nat) :
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

private theorem sum_positive_of_term_positive (a : Nat → Fraction) : ∀ n,
    (∀ i, i<n → 0≤(a i).num) → ∀ i, i<n → 0<(a i).num → 0<(sum a n).num
  | 0, _, i, hi, _ => by omega
  | n+1, ha, i, hi, hp => by
      by_cases hlast : i=n
      · subst i
        change 0 < (Fraction.add (sum a n) (a n)).num
        unfold Fraction.add
        dsimp
        have hs := sum_nonnegative a n (fun j hj => ha j (by omega))
        have ht := hp
        have hleft : 0≤(sum a n).num * (a n).den :=
          Int.mul_nonneg hs (Int.le_of_lt (a n).den_pos)
        have hright : 0<(a n).num * (sum a n).den :=
          Int.mul_pos ht (sum a n).den_pos
        omega
      · have hprev := sum_positive_of_term_positive a n
          (fun j hj => ha j (by omega)) i (by omega) hp
        change 0 < (Fraction.add (sum a n) (a n)).num
        unfold Fraction.add
        dsimp
        have ht := ha n (by omega)
        have hleft : 0<(sum a n).num * (a n).den :=
          Int.mul_pos hprev (a n).den_pos
        have hright : 0≤(a n).num * (sum a n).den :=
          Int.mul_nonneg ht (Int.le_of_lt (sum a n).den_pos)
        omega

/-! A positive cell in a monotone nonnegative graph gives a positive lower
sum. This is the finite arithmetic prerequisite for the zero-base case. The
statement is a project derivation with no external exact-result attribution. -/
theorem lower_sum_positive_of_positive_cell {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0≤(g a).num)
    (i : Nat) (hi : i<p.count)
    (hwidth : 0<(width p i).num) (hheight : 0<(g (p.nodes i)).num) :
    0<(lowerSum g p).num := by
  have hsum := sum_positive_of_term_positive
    (fun k => Fraction.mul (width p k) (g (p.nodes k))) p.count (by
    intro j hj
    have hgj : 0≤(g (p.nodes j)).num :=
      Fraction.nonnegative_of_le hbase (hg _ _ (Fraction.magnitudes.le_refl _)
        (node_bounds p j (by omega)).1 (node_bounds p j (by omega)).2)
    have hwj : 0≤(width p j).num :=
      (difference_nonnegative_iff _ _).mpr (p.ordered j hj)
    exact Fraction.nonnegative_mul _ _ hwj hgj)
  apply hsum i hi
  change 0<(Fraction.mul (width p i) (g (p.nodes i))).num
  unfold Fraction.mul
  dsimp
  exact Int.mul_pos hwidth hheight

/-! A finite ordered partition cannot reach its right endpoint using only
zero-width cells. The result is stated from an already interior node so it
can be combined with a mesh bound without assigning a geometric area. -/
private theorem exists_positive_width_from_aux {a b : Fraction} (p : Partition a b)
    (n j : Nat) (hn : p.count-j=n) (hj : j<p.count)
    (hjb : Fraction.lt (p.nodes j) b) :
    ∃ i, j≤i ∧ i<p.count ∧ 0<(width p i).num := by
  induction n using Nat.strongRecOn generalizing j with
  | ind k ih =>
      by_cases hpos : 0<(width p j).num
      · exact ⟨j, Nat.le_refl _, hj, hpos⟩
      · have hnon : 0≤(width p j).num :=
          (difference_nonnegative_iff _ _).mpr (p.ordered j hj)
        have hzero : (width p j).num=0 := by omega
        have hnode : Fraction.equiv (p.nodes (j+1)) (p.nodes j) := by
          unfold width durationDifference HarmonicStability.negF Fraction.add at hzero
          dsimp at hzero
          simp only [Int.neg_mul] at hzero
          unfold Fraction.equiv
          omega
        have hnext : Fraction.lt (p.nodes (j+1)) b :=
          Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv hnode) hjb
        have hjnext : j+1<p.count := by
          by_cases hnextlt : j+1<p.count
          · exact hnextlt
          · have heq : j+1=p.count := by omega
            have hlast : Fraction.equiv (p.nodes (j+1)) b := by
              simpa [heq] using p.last
            exact False.elim (Fraction.magnitudes.lt_irrefl _
              (Fraction.magnitudes.lt_of_lt_le hnext
                (Fraction.le_of_equiv (Fraction.equiv_symm hlast))))
        obtain ⟨i, hji, hi, hwi⟩ := ih (p.count-(j+1)) (by omega)
          (j+1) (by omega) hjnext hnext
        exact ⟨i, by omega, hi, hwi⟩

private theorem exists_positive_width_from {a b : Fraction} (p : Partition a b)
    (j : Nat) (hj : j<p.count) (hjb : Fraction.lt (p.nodes j) b) :
    ∃ i, j≤i ∧ i<p.count ∧ 0<(width p i).num :=
  exists_positive_width_from_aux p (p.count-j) j rfl hj hjb

private theorem interval_left_gap_le_total (x y z : Fraction)
    (hxy : Fraction.le x y) (hyz : Fraction.le y z) :
    Fraction.le (durationDifference x y) (durationDifference x z) := by
  have h := difference_interval_gaps x y z hxy hyz
  have hxy' := (difference_nonnegative_iff x y).mpr hxy
  have hxz' := (difference_nonnegative_iff x z).mpr
    (Fraction.magnitudes.le_trans hxy hyz)
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.equiv_symm
      (Fraction.abs_of_nonnegative _ hxy')) h.1)
    (Fraction.abs_of_nonnegative _ hxz')

private theorem interval_right_gap_le_total (x y z : Fraction)
    (hxy : Fraction.le x y) (hyz : Fraction.le y z) :
    Fraction.le (durationDifference y z) (durationDifference x z) := by
  have h := difference_interval_gaps x y z hxy hyz
  have hyz' := (difference_nonnegative_iff y z).mpr hyz
  have hxz' := (difference_nonnegative_iff x z).mpr
    (Fraction.magnitudes.le_trans hxy hyz)
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.equiv_symm
      (Fraction.abs_of_nonnegative _ hyz')) h.2)
    (Fraction.abs_of_nonnegative _ hxz')

/-! A positive interior ordinate eventually supplies a positive lower
sum, even when the left endpoint ordinate is zero. The proof uses only
finite partition coverage and the shrinking maximum-width premise: a
midpoint patch cannot be covered forever by zero-width cells. -/
theorem lower_sum_eventually_positive {a b c : Fraction}
    (g : Fraction → Fraction) (parts : Nat → Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0≤(g a).num)
    (hac : Fraction.le a c) (hcb : Fraction.lt c b)
    (hgc : 0<(g c).num)
    (hmesh : ∀ delta : Fraction, 0<delta.num →
      ∃ N : Nat, ∀ m, N≤m → Fraction.lt (maxWidth (parts m)) delta) :
    ∃ N, ∀ m, N≤m → 0<(lowerSum g (parts m)).num := by
  let d : Fraction := midpoint c b
  let delta : Fraction := (durationDifference c b).half
  have hspan : 0<(durationDifference c b).num := by
    unfold durationDifference HarmonicStability.negF Fraction.add at *
    dsimp at *
    simp only [Int.neg_mul] at hcb ⊢
    unfold Fraction.lt at hcb
    omega
  have hdelta : 0<delta.num := by
    simpa [delta, Fraction.half] using hspan
  obtain ⟨N,hN⟩ := hmesh delta hdelta
  refine ⟨N,?_⟩
  intro m hm
  let p := parts m
  have hcb_le : Fraction.le c b := Fraction.magnitudes.lt_implies_le hcb
  have hbetween := midpoint_between c b hcb_le
  have hacd : Fraction.le a d := Fraction.magnitudes.le_trans hac hbetween.1
  obtain ⟨i,hi,hl,hr⟩ := partition_cover p d hacd hbetween.2
  have hmax : Fraction.lt (maxWidth p) delta := hN m hm
  have hnotleft : ¬ Fraction.le (p.nodes i) c := by
    intro hic
    have hleft := interval_right_gap_le_total (p.nodes i) c d hic hbetween.1
    have hcell := interval_left_gap_le_total (p.nodes i) d (p.nodes (i+1)) hl hr
    have hdc : Fraction.le delta (durationDifference (p.nodes i) d) :=
      Fraction.le_equiv_left (Fraction.equiv_symm (midpoint_lower_gap c b)) hleft
    have hwidth : Fraction.le delta (width p i) :=
      Fraction.magnitudes.le_trans hdc hcell
    have hbound := (maxWidth_bounds p).1 i hi
    exact Fraction.magnitudes.lt_irrefl delta
      (Fraction.magnitudes.lt_of_le_lt
        (Fraction.magnitudes.le_trans hwidth hbound) hmax)
  have hci : Fraction.lt c (p.nodes i) := by
    have hle : Fraction.le c (p.nodes i) := by
      by_cases h : Fraction.le c (p.nodes i)
      · exact h
      · have hrev : Fraction.le (p.nodes i) c := by
          unfold Fraction.le at h ⊢
          omega
        exact False.elim (hnotleft hrev)
    have hnot : ¬ Fraction.le (p.nodes i) c := hnotleft
    unfold Fraction.lt
    have hle' := hle
    have hnot' := hnot
    unfold Fraction.le at hle' hnot'
    omega
  have hnext : Fraction.lt (p.nodes (i+1)) b := by
    by_cases hlt : Fraction.lt (p.nodes (i+1)) b
    · exact hlt
    · have hnext_le : Fraction.le (p.nodes (i+1)) b :=
        (node_bounds p (i+1) (by omega)).2
      have hrev : Fraction.le b (p.nodes (i+1)) := by
        have hlt' := hlt
        unfold Fraction.lt at hlt'
        unfold Fraction.le
        omega
      have heq : Fraction.equiv (p.nodes (i+1)) b :=
        (Fraction.equiv_iff_mutual_le _ _).mpr ⟨hnext_le,hrev⟩
      have hleft := interval_right_gap_le_total (p.nodes i) d b hl hbetween.2
      have hdb : Fraction.le delta (durationDifference d b) :=
        Fraction.le_equiv_left (Fraction.equiv_symm (midpoint_upper_gap c b))
          (Fraction.magnitudes.le_refl _)
      have hendpoint : Fraction.equiv (width p i)
          (durationDifference (p.nodes i) b) := by
        exact difference_congr (Fraction.equiv_refl _) heq
      have hdelta_total : Fraction.le delta (durationDifference (p.nodes i) b) :=
        Fraction.magnitudes.le_trans hdb hleft
      have hwidth : Fraction.le delta (width p i) :=
        Fraction.le_equiv_right hdelta_total (Fraction.equiv_symm hendpoint)
      have hbound := (maxWidth_bounds p).1 i hi
      exact False.elim (Fraction.magnitudes.lt_irrefl delta
        (Fraction.magnitudes.lt_of_le_lt
          (Fraction.magnitudes.le_trans hwidth hbound) hmax))
  have hjnext : i+1<p.count := by
    by_cases h : i+1<p.count
    · exact h
    · have heq : i+1=p.count := by omega
      have hlast : Fraction.equiv (p.nodes (i+1)) b := by
        simpa [heq] using p.last
      exact False.elim (Fraction.magnitudes.lt_irrefl _
        (Fraction.magnitudes.lt_of_lt_le hnext
          (Fraction.le_of_equiv (Fraction.equiv_symm hlast))))
  obtain ⟨k,hik,hk,hwidth⟩ := exists_positive_width_from p (i+1) hjnext hnext
  have hnodeik : Fraction.le (p.nodes i) (p.nodes k) :=
    node_order p k i (by omega) (by omega)
  have hck : Fraction.le c (p.nodes k) :=
    Fraction.magnitudes.le_trans (Fraction.magnitudes.lt_implies_le hci) hnodeik
  have hgck : Fraction.le (g c) (g (p.nodes k)) :=
    hg c (p.nodes k) hac hck (node_bounds p k (by omega)).2
  have hheight : 0<(g (p.nodes k)).num := by
    apply (Fraction.positive_iff_zero_lt _).mpr
    exact Fraction.magnitudes.lt_of_lt_le
      ((Fraction.positive_iff_zero_lt _).mp hgc) hgck
  exact lower_sum_positive_of_positive_cell g p hg hbase k hk hwidth hheight

/-! The upper sums inherit eventual positivity from the lower sums. The only
additional input is the finite lower/upper ordering already proved by the
rectangle gap bound. -/
theorem upper_sum_eventually_positive {a b : Fraction}
    (g : Fraction → Fraction) (parts : Nat → Partition a b)
    (hg : MonotoneOn g a b)
    (hlower : ∃ N, ∀ m, N≤m → 0<(lowerSum g (parts m)).num) :
    ∃ N, ∀ m, N≤m → 0<(upperSum g (parts m)).num := by
  obtain ⟨N,hN⟩ := hlower
  refine ⟨N,?_⟩
  intro m hm
  let p := parts m
  have horder : Fraction.le (lowerSum g p) (upperSum g p) := by
    apply sum_mono
    intro i hi
    have hheight : Fraction.le (g (p.nodes i)) (g (p.nodes (i+1))) :=
      hg _ _ (node_bounds p i (by omega)).1 (p.ordered i hi)
        (node_bounds p (i+1) (by omega)).2
    exact Fraction.mul_le_mul_nonnegative_left hheight (width p i)
      ((difference_nonnegative_iff _ _).mpr (p.ordered i hi))
  apply (Fraction.positive_iff_zero_lt _).mpr
  exact Fraction.magnitudes.lt_of_lt_le
    ((Fraction.positive_iff_zero_lt _).mp (hN m hm)) horder

/-- Every lower sum is bounded below by `(b-a)*g(a)`, independently of its
mesh. Source: this English coordinate statement and finite telescoping
proof; no exact external quotation or priority is claimed. Repeated nodes
and equivalent endpoint representations are allowed. -/
theorem lower_sum_base_bound {a b : Fraction} (g : Fraction → Fraction)
    (p : Partition a b) (hg : MonotoneOn g a b) :
    Fraction.le (Fraction.mul (durationDifference a b) (g a)) (lowerSum g p) := by
  have hw : Fraction.equiv (sum (width p) p.count) (durationDifference a b) :=
    Fraction.equiv_trans (sum_telescope p.nodes p.count)
      (difference_congr p.first p.last)
  have he := Fraction.equiv_trans (sum_mul (width p) (g a) p.count)
    (Fraction.equiv_trans (Fraction.mul_equiv_left (g a) hw)
      (Fraction.mul_comm (g a) (durationDifference a b)))
  apply Fraction.le_equiv_left (Fraction.equiv_symm he)
  apply sum_mono
  intro i hi
  exact Fraction.le_equiv_left (Fraction.mul_comm (g a) (width p i))
    (Fraction.mul_le_mul_nonnegative_left
      (hg a (p.nodes i) (Fraction.magnitudes.le_refl _)
        (node_bounds p i (by omega)).1 (node_bounds p i (by omega)).2)
      (width p i) ((difference_nonnegative_iff _ _).mpr (p.ordered i hi)))

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
