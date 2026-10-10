import BarrowLib.Polygon.RationalIntervals
import ModernLib.Foundation.Polygon.ScalarOrder
import ModernLib.Foundation.Polygon.ScaledTolerance

/-! Cauchy realization of nonnegative bounded closed rational cuts by explicit
interval bisection. No scalar completeness field or desired Cauchy condition is
supplied; the shrinking intervals prove it. -/
namespace NewtonLimitDynamics.Polygon.BoundedCuts
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicTimeComparison
open HarmonicTimeRealization HarmonicComparison CauchyValues PositionValues BinaryTime ScalarOrder RationalIntervals

structure Cut where
  lower : Fraction → Prop
  zero_lower : lower (Fraction.ofInt 0)
  downward : ∀ p q, Fraction.le p q → lower q → lower p
  closed : ∀ q, (∀ eps : Fraction, 0 < eps.num →
    ∃ p, lower p ∧ Fraction.le q (Fraction.add p eps)) → lower q
  bound : Fraction
  bound_nonnegative : 0 ≤ bound.num
  bounded : ∀ q, lower q → Fraction.le q bound

noncomputable def step (c : Cut) (p : Fraction × Fraction) : Fraction × Fraction := by
  classical
  exact if c.lower (midpoint p.1 p.2) then (midpoint p.1 p.2,p.2)
    else (p.1,midpoint p.1 p.2)

noncomputable def interval (c : Cut) : Nat → Fraction × Fraction
  | 0 => (Fraction.ofInt 0,c.bound)
  | n+1 => step c (interval c n)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem lower_mem (c : Cut) : ∀ n, c.lower (interval c n).1
  | 0 => c.zero_lower
  | n+1 => by
      classical
      simp only [interval,step]
      split
      · assumption
      · exact lower_mem c n

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem upper_bound (c : Cut) : ∀ n q, c.lower q → Fraction.le q (interval c n).2
  | 0, q, hq => c.bounded q hq
  | n+1, q, hq => by
      classical
      simp only [interval,step]
      split
      · exact upper_bound c n q hq
      · rename_i hm
        apply Classical.byContradiction
        intro hn
        change ¬ Fraction.le q (midpoint (interval c n).1 (interval c n).2) at hn
        have hmid : Fraction.le (midpoint (interval c n).1 (interval c n).2) q := by
          unfold Fraction.le at hn ⊢
          omega
        exact hm (c.downward _ _ hmid hq)

-- Modern dependency score: 2/2 (M=2, H=0; transitive project theorems/axioms).
theorem interval_order (c : Cut) (n : Nat) :
    Fraction.le (interval c n).1 (interval c n).2 :=
  upper_bound c n _ (lower_mem c n)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem half_tail (A : Fraction) (n : Nat) :
    Fraction.equiv (GeometricTail.tailCap A n).half (GeometricTail.tailCap A (n+1)) := by
  simp only [Fraction.equiv,Fraction.half,GeometricTail.tailCap,Int.pow_succ]
  ac_nf

-- Modern dependency score: 1/7 (M=1, H=6; transitive project theorems/axioms).
theorem width_cap (c : Cut) : ∀ n,
    Fraction.equiv (durationDifference (interval c n).1 (interval c n).2)
      (GeometricTail.tailCap c.bound n)
  | 0 => by
      simp [interval,durationDifference,HarmonicStability.negF,GeometricTail.tailCap,
        Fraction.equiv,Fraction.add,Fraction.ofInt]
  | n+1 => by
      classical
      have hh := Fraction.equiv_trans (half_equiv (width_cap c n)) (half_tail c.bound n)
      simp only [interval,step]
      split
      · exact Fraction.equiv_trans (midpoint_upper_gap _ _) hh
      · exact Fraction.equiv_trans (midpoint_lower_gap _ _) hh

-- Modern dependency score: 3/20 (M=3, H=17; transitive project theorems/axioms).
theorem adjacent_bound (c : Cut) (n : Nat) :
    Fraction.le (FiniteEstimates.stateDistance
      (scalarState (interval c (n+1)).1) (scalarState (interval c n).1))
      (GeometricTail.tailCap c.bound (n+1)) := by
  classical
  have hcap : 0 ≤ (GeometricTail.tailCap c.bound (n+1)).num := c.bound_nonnegative
  have hh := Fraction.equiv_trans (midpoint_lower_gap (interval c n).1 (interval c n).2)
    (Fraction.equiv_trans (half_equiv (width_cap c n)) (half_tail c.bound n))
  simp only [interval,step]
  split
  · exact Fraction.le_of_equiv (Fraction.equiv_trans (scalarState_distance _ _)
      (Fraction.equiv_trans (Fraction.abs_equiv hh)
        (Fraction.abs_of_nonnegative _ hcap)))
  · exact Fraction.le_equiv_left (FiniteEstimates.stateDistance_self_zero _)
      (by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hcap)

noncomputable def name (c : Cut) : EndpointCauchyName where
  approx := fun n => scalarState (interval c n).1
  cauchy := by
    intro eps heps
    refine ⟨GeometricTail.modulus c.bound eps,?_⟩
    intro m n hm hn
    exact Fraction.magnitudes.lt_of_le_lt
      (GeometricTail.two_sided (fun k => scalarState (interval c k).1) c.bound
        c.bound_nonnegative (adjacent_bound c) (GeometricTail.modulus c.bound eps) m n hm hn)
      (GeometricTail.doubleTail_lt_tolerance c.bound eps c.bound_nonnegative heps)

-- Modern dependency score: 6/49 (M=6, H=43; transitive project theorems/axioms).
theorem name_realizes_cut (c : Cut) (q : Fraction) : NameBelow q (name c) ↔ c.lower q := by
  constructor
  · intro h
    apply c.closed q
    intro eps heps
    obtain ⟨N,hN⟩ := h eps heps
    exact ⟨(interval c N).1,lower_mem c N,hN N (Nat.le_refl _)⟩
  · intro hq eps heps
    obtain ⟨N,hN⟩ := duration_eventually_small c.bound eps c.bound_nonnegative heps
    refine ⟨N,?_⟩
    intro n hn
    have hwidth := Fraction.le_equiv_left (width_cap c n)
      (Fraction.magnitudes.lt_implies_le (hN n hn))
    have hupper := Fraction.le_equiv_right (upper_bound c n q hq)
      (Fraction.equiv_symm (add_difference_cancel (interval c n).1 (interval c n).2))
    exact Fraction.magnitudes.le_trans hupper
      (Fraction.add_le_add_left hwidth (interval c n).1)

noncomputable def value (c : Cut) : ScalarValue := ⟨realize (name c),by rfl⟩

-- Modern dependency score: 21/74 (M=21, H=53; transitive project theorems/axioms).
theorem value_realizes_cut (c : Cut) (q : Fraction) : Below q (value c).val ↔ c.lower q :=
  name_realizes_cut c q

-- Modern dependency score: 22/75 (M=22, H=53; transitive project theorems/axioms).
theorem value_nonnegative (c : Cut) : Below (Fraction.ofInt 0) (value c).val :=
  (value_realizes_cut c _).mpr c.zero_lower

-- Modern dependency score: 22/75 (M=22, H=53; transitive project theorems/axioms).
theorem value_bound (c : Cut) (q : Fraction) (hq : Below q (value c).val) :
    Fraction.le q c.bound := c.bounded q ((value_realizes_cut c q).mp hq)

-- Modern dependency score: 3/18 (M=3, H=15; transitive project theorems/axioms).
theorem lower_nonnegative (c : Cut) : ∀ n, 0 ≤ (interval c n).1.num
  | 0 => by simp [interval,Fraction.ofInt]
  | n+1 => by
      classical
      have hlo := lower_nonnegative c n
      have h0 : Fraction.le (Fraction.ofInt 0) (interval c n).1 := by
        simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hlo
      have hm : Fraction.le (Fraction.ofInt 0)
          (midpoint (interval c n).1 (interval c n).2) :=
        Fraction.magnitudes.le_trans h0 (midpoint_between _ _ (interval_order c n)).1
      simp only [interval,step]
      split
      · simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hm
      · exact hlo

-- Modern dependency score: 30/83 (M=30, H=53; transitive project theorems/axioms).
theorem value_within_zero (c : Cut) :
    Within (value c).val (embed (scalarState (Fraction.ofInt 0))) c.bound := by
  apply nameBound_of_eventual_le _ _ _ 0
  intro n _
  have he := Fraction.equiv_trans (scalarState_distance (interval c n).1 (Fraction.ofInt 0))
    (Fraction.equiv_trans (Fraction.abs_equiv (show
      Fraction.equiv (durationDifference (Fraction.ofInt 0) (interval c n).1)
        (interval c n).1 by
      simp [durationDifference,HarmonicStability.negF,Fraction.equiv,Fraction.add,Fraction.ofInt]))
      (Fraction.abs_of_nonnegative _ (lower_nonnegative c n)))
  exact Fraction.le_equiv_left he (c.bounded _ (lower_mem c n))

-- Modern dependency score: 2/10 (M=2, H=8; transitive project theorems/axioms).
theorem abs_width_cap (c : Cut) (n : Nat) :
    Fraction.equiv (durationDifference (interval c n).1 (interval c n).2).abs
      (GeometricTail.tailCap c.bound n) :=
  Fraction.equiv_trans (Fraction.abs_equiv (width_cap c n))
    (Fraction.abs_of_nonnegative _ c.bound_nonnegative)

/-- Different initial upper budgets cannot change the completed content. -/
-- Modern dependency score: 6/35 (M=6, H=29; transitive project theorems/axioms).
theorem names_gap (c d : Cut) (heq : ∀ q, c.lower q ↔ d.lower q) (n : Nat) :
    Fraction.le (FiniteEstimates.stateDistance
      (scalarState (interval c n).1) (scalarState (interval d n).1))
      (GeometricTail.tailCap (Fraction.add c.bound d.bound) n) := by
  have hcd := upper_bound d n _ ((heq _).mp (lower_mem c n))
  have hdc := upper_bound c n _ ((heq _).mpr (lower_mem d n))
  have hsum : Fraction.le (FiniteEstimates.stateDistance
      (scalarState (interval c n).1) (scalarState (interval d n).1))
      (Fraction.add (GeometricTail.tailCap c.bound n) (GeometricTail.tailCap d.bound n)) := by
    by_cases horder : Fraction.le (interval d n).1 (interval c n).1
    · have hg := (difference_interval_gaps (interval d n).1 (interval c n).1
        (interval d n).2 horder hcd).1
      have hb := Fraction.le_equiv_right hg (abs_width_cap d n)
      have hlast := Fraction.le_equiv_right
        (Fraction.le_add_nonnegative (GeometricTail.tailCap d.bound n)
          (GeometricTail.tailCap c.bound n) c.bound_nonnegative)
        (Fraction.add_comm _ _)
      exact Fraction.le_equiv_left (scalarState_distance _ _) (Fraction.magnitudes.le_trans hb hlast)
    · have hreverse : Fraction.le (interval c n).1 (interval d n).1 := by
        unfold Fraction.le at horder ⊢
        omega
      have hg := (difference_interval_gaps (interval c n).1 (interval d n).1
        (interval c n).2 hreverse hdc).1
      have hb := Fraction.le_equiv_right hg (abs_width_cap c n)
      have hlast := Fraction.le_add_nonnegative (GeometricTail.tailCap c.bound n)
        (GeometricTail.tailCap d.bound n) d.bound_nonnegative
      have hbound := Fraction.le_equiv_left (scalarState_distance _ _)
        (Fraction.magnitudes.le_trans hb hlast)
      exact Fraction.le_equiv_left (FiniteEstimates.stateDistance_symm _ _) hbound
  exact Fraction.le_equiv_right hsum (GeometricTail.tail_add c.bound d.bound n)

-- Modern dependency score: 8/56 (M=8, H=48; transitive project theorems/axioms).
theorem name_equiv_of_lower_iff (c d : Cut) (heq : ∀ q, c.lower q ↔ d.lower q) :
    NameEquiv (name c) (name d) := by
  intro eps heps
  obtain ⟨N,hN⟩ := duration_eventually_small (Fraction.add c.bound d.bound) eps
    (Fraction.nonnegative_add _ _ c.bound_nonnegative d.bound_nonnegative) heps
  exact ⟨N,fun n hn => Fraction.magnitudes.lt_of_le_lt (names_gap c d heq n) (hN n hn)⟩

-- Modern dependency score: 20/73 (M=20, H=53; transitive project theorems/axioms).
theorem value_eq_of_lower_iff (c d : Cut) (heq : ∀ q, c.lower q ↔ d.lower q) :
    value c = value d := Subtype.ext (Quotient.sound (name_equiv_of_lower_iff c d heq))

-- Modern dependency score: 35/88 (M=35, H=53; transitive project theorems/axioms).
theorem value_zero_of_bound_zero (c : Cut) (hz : c.bound.num = 0) :
    (value c).val = embed (scalarState (Fraction.ofInt 0)) := by
  apply (within_zero_iff _ _).mp
  exact HarmonicTimeRealization.within_mono _ _ _ _
    (Fraction.le_of_equiv (show Fraction.equiv c.bound (Fraction.ofInt 0) by
      simp [Fraction.equiv,Fraction.ofInt,hz])) (value_within_zero c)

-- Modern dependency score: 18/70 (M=18, H=52; transitive project theorems/axioms).
theorem value_of_rational_cut (c : Cut) (r : Fraction)
    (hr : ∀ q, c.lower q ↔ Fraction.le q r) :
    (value c).val = embed (scalarState r) := by
  apply Quotient.sound
  intro eps heps
  obtain ⟨N,hN⟩ := duration_eventually_small c.bound eps c.bound_nonnegative heps
  refine ⟨N,?_⟩
  intro n hn
  have hl := (hr _).mp (lower_mem c n)
  have hu := upper_bound c n r ((hr r).mpr (Fraction.le_of_equiv (Fraction.equiv_refl _)))
  have hg := (difference_interval_gaps (interval c n).1 r (interval c n).2 hl hu).1
  have hb := Fraction.le_equiv_right hg (abs_width_cap c n)
  have hd := Fraction.le_equiv_left (scalarState_distance r (interval c n).1) hb
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_equiv_left (FiniteEstimates.stateDistance_symm _ _) hd) (hN n hn)

def rationalCut (r B : Fraction) (hr : 0 ≤ r.num) (hB : 0 ≤ B.num)
    (hrB : Fraction.le r B) : Cut where
  lower := fun q => Fraction.le q r
  zero_lower := by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hr
  downward := fun _ _ hpq hq => Fraction.magnitudes.le_trans hpq hq
  closed := by
    intro q h
    apply (Fraction.le_iff_toRat _ _).mpr
    apply Rational.le_of_enlargements
    intro epsR hepsR
    let eps := Fraction.ofRat epsR
    have heps : 0 < eps.num := (Fraction.positive_iff_toRat eps).mpr
      (by simpa only [eps, Fraction.toRat_ofRat] using hepsR)
    rw [← Fraction.toRat_ofRat epsR, ← Fraction.toRat_add]
    apply (Fraction.le_iff_toRat _ _).mp
    change Fraction.le _ (Fraction.add _ eps)
    obtain ⟨p,hp,hqp⟩ := h eps heps
    exact Fraction.magnitudes.le_trans hqp (Fraction.add_le_add_right hp eps)
  bound := B
  bound_nonnegative := hB
  bounded := fun _ hq => Fraction.magnitudes.le_trans hq hrB

-- Modern dependency score: 19/77 (M=19, H=58; transitive project theorems/axioms).
theorem rationalCut_value (r B : Fraction) (hr : 0 ≤ r.num) (hB : 0 ≤ B.num)
    (hrB : Fraction.le r B) :
    (value (rationalCut r B hr hB hrB)).val = embed (scalarState r) :=
  value_of_rational_cut _ r (fun _ => Iff.rfl)

private def oneThird : Fraction := ⟨1,3,by decide⟩
private def firstControl : Cut := rationalCut oneThird (Fraction.ofInt 1)
  (by decide) (by decide) (by unfold Fraction.le oneThird Fraction.ofInt; decide)
private def secondControl : Cut := rationalCut oneThird (Fraction.ofInt 2)
  (by decide) (by decide) (by unfold Fraction.le oneThird Fraction.ofInt; decide)

/-- A known nonzero content cut recovers its rational value with different budgets. -/
-- Modern dependency score: 20/78 (M=20, H=58; transitive project theorems/axioms).
theorem one_third_control_value : (value firstControl).val = embed (scalarState oneThird) :=
  rationalCut_value _ _ _ _ _

-- Modern dependency score: 21/80 (M=21, H=59; transitive project theorems/axioms).
theorem one_third_different_budgets : value firstControl = value secondControl :=
  value_eq_of_lower_iff _ _ (fun _ => Iff.rfl)

end NewtonLimitDynamics.Polygon.BoundedCuts
