import BarrowLib.Polygon.MonotoneRectangles
import BarrowLib.Common.Exhaustion

/-! Finite rectangle-union area from explicit elementary area rules.
`AreaRules` is a supplied geometric convention, not an existence theorem for
area on arbitrary figures. It is a partial relation: no rational area for an
arbitrary curved or unbounded set is postulated. Additivity applies only to
sets separated by a vertical cut, permitting a shared boundary of zero area.
The separation of adjacent partition cells is proved below. -/
namespace NewtonLimitDynamics.Polygon.RectangleContent
open NewtonLimitDynamics TimeSubdivision MonotoneRectangles PolygonFanArea

structure AreaRules where
  HasArea : (Point → Prop) → Fraction → Prop
  empty : HasArea (fun _ => False) (Fraction.ofInt 0)
  congr_set : ∀ U V A, (∀ x, U x ↔ V x) → HasArea U A → HasArea V A
  congr_value : ∀ U A B, Fraction.equiv A B → HasArea U A → HasArea U B
  rectangle : ∀ l r H, Fraction.le l r → 0 ≤ H.num →
    HasArea (MonotoneRectangles.rectangle l r H)
      (Fraction.mul (HarmonicTimeComparison.durationDifference l r) H)
  separated_union : ∀ U V A B c,
    (∀ x, U x → Fraction.le x.1 c) → (∀ x, V x → Fraction.le c x.1) →
    HasArea U A → HasArea V B → HasArea (fun x => U x ∨ V x) (Fraction.add A B)
  monotone : ∀ U V A B, (∀ x, U x → V x) → HasArea U A → HasArea V B → Fraction.le A B

def strips {a b : Fraction} (p : Partition a b) (heights : Nat → Fraction)
    (n : Nat) (x : Point) : Prop :=
  ∃ i, i < n ∧ MonotoneRectangles.rectangle (p.nodes i) (p.nodes (i+1)) (heights i) x

theorem strips_succ {a b : Fraction} (p : Partition a b) (heights : Nat → Fraction)
    (n : Nat) (x : Point) :
    strips p heights (n+1) x ↔ strips p heights n x ∨
      MonotoneRectangles.rectangle (p.nodes n) (p.nodes (n+1)) (heights n) x := by
  constructor
  · rintro ⟨i, hi, hx⟩
    by_cases h : i < n
    · exact Or.inl ⟨i, h, hx⟩
    · have he : i = n := by omega
      subst i
      exact Or.inr hx
  · intro h
    rcases h with ⟨i, hi, hx⟩ | hx
    · exact ⟨i, by omega, hx⟩
    · exact ⟨n, by omega, hx⟩

/-- The actual finite union has its side-product sum as area. Repeated
nodes cause zero-width rectangles; no division or distinct-node premise is
used. The only geometric area assumptions are the displayed `AreaRules`. -/
theorem strips_area (area : AreaRules) {a b : Fraction} (p : Partition a b)
    (heights : Nat → Fraction) (hh : ∀ i, i < p.count → 0 ≤ (heights i).num)
    (n : Nat) (hn : n ≤ p.count) :
    area.HasArea (strips p heights n)
      (sum (fun i => Fraction.mul (width p i) (heights i)) n) := by
  induction n with
  | zero =>
    apply area.congr_set (fun _ => False) _ _ _ area.empty
    intro x
    simp only [strips, Nat.not_lt_zero, false_and, exists_false]
  | succ n ih =>
    have hp := ih (by omega)
    have hr := area.rectangle (p.nodes n) (p.nodes (n+1)) (heights n)
      (p.ordered n (by omega)) (hh n (by omega))
    have hu := area.separated_union _ _ _ _ (p.nodes n) ?_ ?_ hp hr
    · exact area.congr_set _ _ _ (fun x => (strips_succ p heights n x).symm) hu
    · intro x hx
      obtain ⟨i, hi, _, hright, _⟩ := hx
      exact Fraction.magnitudes.le_trans hright (node_order p n (i+1) (by omega) (by omega))
    · intro x hx
      exact hx.1

theorem lower_upper_areas (area : AreaRules) (g : Fraction → Fraction) (a b : Fraction)
    (p : Partition a b) (hg : MonotoneOn g a b) (hbase : 0 ≤ (g a).num) :
    area.HasArea (lowerFigure g p) (lowerSum g p) ∧
      area.HasArea (upperFigure g p) (upperSum g p) := by
  have hheight (i : Nat) (hi : i ≤ p.count) : 0 ≤ (g (p.nodes i)).num :=
    Fraction.nonnegative_of_le hbase (hg a (p.nodes i) (Fraction.magnitudes.le_refl _)
      (node_bounds p i hi).1 (node_bounds p i hi).2)
  exact ⟨strips_area area p (fun i => g (p.nodes i)) (fun i hi => hheight i (by omega)) _ (Nat.le_refl _),
    strips_area area p (fun i => g (p.nodes (i+1))) (fun i hi => hheight (i+1) (by omega)) _ (Nat.le_refl _)⟩

/-- If the given curved region has an assigned rational area, its numeric
enclosure follows from proved set inclusion and the geometric area rules.
The existence or rationality of a curved region's area is not asserted. -/
theorem curved_area_enclosure (area : AreaRules) (g : Fraction → Fraction) (a b A : Fraction)
    (p : Partition a b) (hg : MonotoneOn g a b) (hbase : 0 ≤ (g a).num)
    (hA : area.HasArea (figure g a b) A) :
    Fraction.le (lowerSum g p) A ∧ Fraction.le A (upperSum g p) := by
  have ha := lower_upper_areas area g a b p hg hbase
  have hs := figure_enclosure g p hg
  exact ⟨area.monotone _ _ _ _ hs.1 ha.1 hA, area.monotone _ _ _ _ hs.2 hA ha.2⟩

/-- Equal-width exhaustion uses the exact telescoping gap identity supplied
by the owning historical Lemma II, rather than the unequal-width bound. -/
theorem equal_width_exhaustion (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → Partition a b) (hg : MonotoneOn g a b) (mesh : Nat → Fraction)
    (hwidth : ∀ m i, i < (parts m).count → Fraction.equiv (width (parts m) i) (mesh m))
    (hidentity : ∀ m, Fraction.equiv (gap g (parts m))
      (Fraction.mul (mesh m) (HarmonicTimeComparison.durationDifference (g a) (g b))))
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes mesh) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun m => gap g (parts m)) := by
  have hab : Fraction.le a b := Fraction.magnitudes.le_trans
    (node_bounds (parts 0) 0 (by omega)).1 (node_bounds (parts 0) 0 (by omega)).2
  let H := HarmonicTimeComparison.durationDifference (g a) (g b)
  have hH : 0 ≤ H.num := (HarmonicTimeComparison.difference_nonnegative_iff _ _).mpr
    (hg a b (Fraction.magnitudes.le_refl _) hab (Fraction.magnitudes.le_refl _))
  intro eps heps
  obtain ⟨N, hN⟩ := hmesh (Fraction.ofRat (HarmonicTimeRealization.factorDelta (H).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat H).mp hH)))
    ((by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat H).mp hH)
        have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
  refine ⟨N, fun m hm => ?_⟩
  have hn : 0 ≤ (mesh m).num := Fraction.nonnegative_equiv
    (Fraction.equiv_symm (hwidth m 0 (parts m).positive_count))
    ((HarmonicTimeComparison.difference_nonnegative_iff _ _).mpr
      ((parts m).ordered 0 (parts m).positive_count))
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv (hidentity m))
    ((show Fraction.lt (Fraction.mul ((mesh m)) (H)) (eps) from by
        apply (Fraction.lt_iff_toRat _ _).mpr
        rw [Fraction.toRat_mul]
        have hcoef := ((Fraction.nonnegative_iff_toRat H).mp hH)
        have hdist := ((Fraction.nonnegative_iff_toRat (mesh m)).mp hn)
        have hstrict := (Fraction.lt_iff_toRat _ _).mp (hN m hm)
        change Fraction.toRat _ < (Fraction.ofRat _).toRat at hstrict
        rw [Fraction.toRat_ofRat] at hstrict
        (try dsimp only at hcoef hdist hstrict ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff]))

/-- Numeric area errors shrink because the represented sets enclose the
given figure. Neither an area-error bound nor its vanishing is a premise. -/
theorem area_errors_vanish (g : Fraction → Fraction) (a b A : Fraction)
    (parts : Nat → Partition a b) (hg : MonotoneOn g a b)
    (henclose : ∀ m, Fraction.le (lowerSum g (parts m)) A ∧ Fraction.le A (upperSum g (parts m)))
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes (fun m => gap g (parts m))) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (lowerSum g (parts m)) A).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (upperSum g (parts m))).abs) := by
  have bound (m : Nat) := HarmonicTimeComparison.difference_interval_gaps
    (lowerSum g (parts m)) A (upperSum g (parts m)) (henclose m).1 (henclose m).2
  have hnonnegative (m : Nat) : 0 ≤ (gap g (parts m)).num :=
    (gap_bound g (parts m) hg (maxWidth (parts m)) (maxWidth_bounds (parts m)).1).1
  constructor <;> intro eps heps <;> obtain ⟨N, hN⟩ := hgap eps heps <;>
    refine ⟨N, fun m hm => ?_⟩
  · exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_equiv_right (bound m).1 (Fraction.abs_of_nonnegative _ (hnonnegative m))) (hN m hm)
  · exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_equiv_right (bound m).2 (Fraction.abs_of_nonnegative _ (hnonnegative m))) (hN m hm)

/-- Ratio to a fixed, separately assigned positive rational area.
Positivity is required before division; zero figures are excluded here. -/
def ratioTo (A : Fraction) (hA : 0 < A.num) (X : Fraction) : Fraction :=
  Fraction.mul X ⟨A.den, A.num, hA⟩

theorem ratio_error (A : Fraction) (hA : 0 < A.num) (X : Fraction) :
    Fraction.equiv (HarmonicTimeComparison.durationDifference (ratioTo A hA X) (Fraction.ofInt 1)).abs
      (Fraction.mul (HarmonicTimeComparison.durationDifference X A).abs ⟨A.den,A.num,hA⟩) := by
  have he : Fraction.equiv
      (HarmonicTimeComparison.durationDifference (ratioTo A hA X) (Fraction.ofInt 1))
      (Fraction.mul (HarmonicTimeComparison.durationDifference X A) ⟨A.den,A.num,hA⟩) := by
    simp only [ratioTo, HarmonicTimeComparison.durationDifference, HarmonicStability.negF,
      Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.mul_one, Int.one_mul]
    ac_nf
  exact Fraction.equiv_trans (Fraction.abs_equiv he)
    (by
      have hi := Fraction.abs_eq_of_nonnegative (⟨A.den,A.num,hA⟩ : Fraction)
        (Int.le_of_lt A.den_pos)
      simpa only [hi] using
        Fraction.abs_mul (HarmonicTimeComparison.durationDifference X A) ⟨A.den,A.num,hA⟩)

/-- Absolute area exhaustion implies a unit ultimate ratio to a fixed
positive assigned area. No ratio to a vanishing denominator is asserted. -/
theorem ratios_approach_one (A : Fraction) (hA : 0 < A.num) (X : Nat → Fraction)
    (hx : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (X m) A).abs)) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (ratioTo A hA (X m)) (Fraction.ofInt 1)).abs) := by
  let C : Fraction := ⟨A.den,A.num,hA⟩
  have hC : 0 ≤ C.num := Int.le_of_lt A.den_pos
  intro eps heps
  obtain ⟨N,hN⟩ := hx (Fraction.ofRat (HarmonicTimeRealization.factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC)))
    ((by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
  refine ⟨N, fun m hm => ?_⟩
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv (ratio_error A hA (X m)))
    ((show Fraction.lt (Fraction.mul ((HarmonicTimeComparison.durationDifference (X m) A).abs) (C)) (eps) from by
        apply (Fraction.lt_iff_toRat _ _).mpr
        rw [Fraction.toRat_mul]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hdist := ((Fraction.nonnegative_iff_toRat (HarmonicTimeComparison.durationDifference (X m) A).abs).mp (Fraction.abs_num_nonnegative (HarmonicTimeComparison.durationDifference (X m) A)))
        have hstrict := (Fraction.lt_iff_toRat _ _).mp (hN m hm)
        change Fraction.toRat _ < (Fraction.ofRat _).toRat at hstrict
        rw [Fraction.toRat_ofRat] at hstrict
        (try dsimp only at hcoef hdist hstrict ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff]))

theorem area_ratios_approach_one (A : Fraction) (hA : 0 < A.num)
    (L U : Nat → Fraction)
    (hl : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (L m) A).abs))
    (hu : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference A (U m)).abs)) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (ratioTo A hA (L m)) (Fraction.ofInt 1)).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (ratioTo A hA (U m)) (Fraction.ofInt 1)).abs) := by
  refine ⟨ratios_approach_one A hA L hl, ratios_approach_one A hA U ?_⟩
  intro eps heps
  obtain ⟨N,hN⟩ := hu eps heps
  exact ⟨N, fun m hm => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (HarmonicTimeRealization.durationDifference_abs_symm (U m) A))
    (hN m hm)⟩

/-! Mutual ratios of varying finite areas. Source of the precise statements
and proofs: the English coordinate derivation below, using finite telescoping,
positive rational division and exhaustion. This records project provenance,
without an external exact-result attribution or a priority claim. No curved
area, completed quantity or reciprocal-limit theorem is supplied. -/

/-- Both positive varying magnitudes have mutual ratios approaching one.
The denominator-positivity proofs are conclusions, rather than extra inputs. -/
def MutualRatiosOne (L U : Nat → Fraction) : Prop :=
  ∃ (hL : ∀ m, 0 < (L m).num) (hU : ∀ m, 0 < (U m).num),
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (ratioTo (U m) (hU m) (L m)) (Fraction.ofInt 1)).abs) ∧
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference
        (ratioTo (L m) (hL m) (U m)) (Fraction.ofInt 1)).abs)

/-- Ratios are defined and approach one on an actual tail. The offset is
returned as data; every index `N+m` lies in that tail. Initial sums may vanish. -/
def EventuallyMutualRatiosOne (L U : Nat → Fraction) : Prop :=
  ∃ N, MutualRatiosOne (fun m => L (N+m)) (fun m => U (N+m))

private theorem varying_ratio_error_bound (B D X : Fraction)
    (hB : 0 < B.num) (hD : 0 < D.num) (hBD : Fraction.le B D) :
    Fraction.le
      (HarmonicTimeComparison.durationDifference (ratioTo D hD X) (Fraction.ofInt 1)).abs
      (Fraction.mul (HarmonicTimeComparison.durationDifference X D).abs
        (⟨B.den, B.num, hB⟩ : Fraction)) := by
  have hi : Fraction.le (⟨D.den, D.num, hD⟩ : Fraction) ⟨B.den, B.num, hB⟩ := by
    change D.den * B.num ≤ B.den * D.num
    simpa only [Fraction.le, Int.mul_comm] using hBD
  exact Fraction.le_equiv_left (ratio_error D hD X)
    (Fraction.mul_le_mul_nonnegative_left hi _ (Fraction.abs_num_nonnegative _))

/-- A fixed positive lower bound on both denominators turns absolute gap
exhaustion into mutual-ratio exhaustion. The magnitudes themselves may vary. -/
theorem varying_ratios_approach_one (B : Fraction) (hB : 0 < B.num)
    (L U : Nat → Fraction) (hBL : ∀ m, Fraction.le B (L m))
    (hBU : ∀ m, Fraction.le B (U m))
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (L m) (U m)).abs)) :
    MutualRatiosOne L U := by
  have positive (X : Fraction) (hBX : Fraction.le B X) : 0 < X.num :=
    (Fraction.positive_iff_zero_lt X).mpr
      (Fraction.magnitudes.lt_of_lt_le ((Fraction.positive_iff_zero_lt B).mp hB) hBX)
  let hL := fun m => positive (L m) (hBL m)
  let hU := fun m => positive (U m) (hBU m)
  let C : Fraction := ⟨B.den, B.num, hB⟩
  have hC : 0 ≤ C.num := Int.le_of_lt B.den_pos
  have boundL (m : Nat) := varying_ratio_error_bound B (U m) (L m) hB (hU m) (hBU m)
  have boundU (m : Nat) : Fraction.le
      (HarmonicTimeComparison.durationDifference (ratioTo (L m) (hL m) (U m)) (Fraction.ofInt 1)).abs
      (Fraction.mul (HarmonicTimeComparison.durationDifference (L m) (U m)).abs C) :=
    Fraction.le_equiv_right
      (varying_ratio_error_bound B (L m) (U m) hB (hL m) (hBL m))
      (Fraction.mul_equiv_right C
        (HarmonicTimeRealization.durationDifference_abs_symm (U m) (L m)))
  refine ⟨hL, hU, ?_, ?_⟩
  all_goals
    intro eps heps
    obtain ⟨N, hN⟩ := hgap (Fraction.ofRat (HarmonicTimeRealization.factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC)))
      ((by
          apply (Fraction.positive_iff_toRat _).mpr
          change 0 < (Fraction.ofRat _).toRat
          rw [Fraction.toRat_ofRat]
          have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
          have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
          (try dsimp only at hcoef hepsRat ⊢)
          grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
    refine ⟨N, fun m hm => ?_⟩
    have hc := (show Fraction.lt (Fraction.mul ((HarmonicTimeComparison.durationDifference (L m) (U m)).abs) (C)) (eps) from by
        apply (Fraction.lt_iff_toRat _ _).mpr
        rw [Fraction.toRat_mul]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hdist := ((Fraction.nonnegative_iff_toRat (HarmonicTimeComparison.durationDifference (L m) (U m)).abs).mp (Fraction.abs_num_nonnegative (HarmonicTimeComparison.durationDifference (L m) (U m))))
        have hstrict := (Fraction.lt_iff_toRat _ _).mp (hN m hm)
        change Fraction.toRat _ < (Fraction.ofRat _).toRat at hstrict
        rw [Fraction.toRat_ofRat] at hstrict
        (try dsimp only at hcoef hdist hstrict ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff])
  · exact Fraction.magnitudes.lt_of_le_lt (boundL m) hc
  · exact Fraction.magnitudes.lt_of_le_lt (boundU m) hc

/-- Restrict the existing mutual-ratio proof to a tail with uniform positive
denominator bounds. Source: this project derivation and its English statement;
no exact historical attribution or priority is claimed. -/
theorem varying_ratios_approach_one_eventually (B : Fraction) (hB : 0 < B.num)
    (L U : Nat → Fraction) (N : Nat)
    (hBL : ∀ m, N≤m → Fraction.le B (L m))
    (hBU : ∀ m, N≤m → Fraction.le B (U m))
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (HarmonicTimeComparison.durationDifference (L m) (U m)).abs)) :
    EventuallyMutualRatiosOne L U := by
  refine ⟨N, varying_ratios_approach_one B hB _ _
    (fun m => hBL (N+m) (by omega)) (fun m => hBU (N+m) (by omega)) ?_⟩
  intro eps heps
  obtain ⟨K,hK⟩ := hgap eps heps
  exact ⟨K,fun m hm => hK (N+m) (by omega)⟩

/-- A nonzero horizontal interval and positive starting ordinate derive the
uniform denominator bound `(b-a)*g(a)`. No curved-area assignment is used. -/
theorem rectangle_mutual_ratios (g : Fraction → Fraction) (a b : Fraction)
    (parts : Nat → Partition a b) (hg : MonotoneOn g a b)
    (hab : Fraction.lt a b) (hbase : 0 < (g a).num)
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => gap g (parts m))) :
    MutualRatiosOne (fun m => lowerSum g (parts m)) (fun m => upperSum g (parts m)) := by
  let B := Fraction.mul (HarmonicTimeComparison.durationDifference a b) (g a)
  have hspan : 0 < (HarmonicTimeComparison.durationDifference a b).num := by
    simp only [HarmonicTimeComparison.durationDifference, HarmonicStability.negF,
      Fraction.add, Int.neg_mul]
    unfold Fraction.lt at hab
    omega
  have hB : 0 < B.num := Int.mul_pos hspan hbase
  have hBL (m : Nat) : Fraction.le B (lowerSum g (parts m)) := lower_sum_base_bound g (parts m) hg
  have hnon (m : Nat) : 0 ≤ (gap g (parts m)).num :=
    (gap_bound g (parts m) hg (maxWidth (parts m)) (maxWidth_bounds (parts m)).1).1
  apply varying_ratios_approach_one B hB _ _ hBL
  · intro m
    exact Fraction.magnitudes.le_trans (hBL m)
      ((HarmonicTimeComparison.difference_nonnegative_iff _ _).mp (hnon m))
  · intro eps heps
    obtain ⟨N, hN⟩ := hgap eps heps
    exact ⟨N, fun m hm => Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.abs_of_nonnegative _ (hnon m))) (hN m hm)⟩

/-- An interior positive ordinate supplies a fixed rectangle below every
upper cover. Once the finite gap is below half its area, that half-area bounds
both sums, including for a zero base ordinate. Source: this English coordinate
statement and the checked containment/cancellation proof, without an external
exact-result attribution or priority claim. The geometric area rules are
explicit; no curved-area assignment or nesting of partitions is used. -/
theorem rectangle_interior_denominator_bound (area : AreaRules)
    (g : Fraction → Fraction) (a b c : Fraction)
    (parts : Nat → Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0≤(g a).num) (hac : Fraction.le a c)
    (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => gap g (parts m))) :
    ∃ B : Fraction, 0<B.num ∧ ∃ N, ∀ m, N≤m →
      Fraction.le B (lowerSum g (parts m)) ∧
      Fraction.le B (upperSum g (parts m)) := by
  let R := Fraction.mul (HarmonicTimeComparison.durationDifference c b) (g c)
  have hspan : 0<(HarmonicTimeComparison.durationDifference c b).num := by
    simp only [HarmonicTimeComparison.durationDifference, HarmonicStability.negF,
      Fraction.add, Int.neg_mul]
    unfold Fraction.lt at hcb
    omega
  have hR : 0<R.num := Int.mul_pos hspan hgc
  have hRU (m : Nat) : Fraction.le R (upperSum g (parts m)) := by
    apply area.monotone _ _ _ _ ?_
      (area.rectangle c b (g c) (Fraction.magnitudes.lt_implies_le hcb)
        (Int.le_of_lt hgc))
      (lower_upper_areas area g a b (parts m) hg hbase).2
    intro x hx
    apply (figure_enclosure g (parts m) hg).2 x
    exact ⟨Fraction.magnitudes.le_trans hac hx.1,hx.2.1,hx.2.2.1,
      Fraction.magnitudes.le_trans hx.2.2.2 (hg c x.1 hac hx.1 hx.2.1)⟩
  obtain ⟨N,hN⟩ := hgap R.half hR
  refine ⟨R.half,hR,N,fun m hm => ?_⟩
  have hsmall : Fraction.le (gap g (parts m)) R.half :=
    Fraction.magnitudes.lt_implies_le (hN m hm)
  have hsum : Fraction.le R (Fraction.add (lowerSum g (parts m)) R.half) :=
    Fraction.magnitudes.le_trans
      (Fraction.le_equiv_right (hRU m)
        (Fraction.equiv_symm (HarmonicTimeComparison.add_difference_cancel
          (lowerSum g (parts m)) (upperSum g (parts m)))))
      (Fraction.add_le_add_left hsmall _)
  have hL : Fraction.le R.half (lowerSum g (parts m)) :=
    Fraction.le_add_cancel_left R.half R.half (lowerSum g (parts m))
      (Fraction.le_equiv_left (Fraction.half_add_self R)
        (Fraction.le_equiv_right hsum (Fraction.add_comm _ _)))
  exact ⟨hL,Fraction.magnitudes.le_trans hL
    ((HarmonicTimeComparison.difference_nonnegative_iff _ _).mp
      (gap_bound g (parts m) hg (maxWidth (parts m))
        (maxWidth_bounds (parts m)).1).1)⟩

/-- The finite lower and upper areas have mutual ratios tending to one on
an actual tail whenever the figure has a positive interior rectangle.
Initial zero denominators are allowed. The fixed denominator bound is derived,
not supplied, and a rational area for the curved figure is unnecessary. -/
theorem rectangle_mutual_ratios_interior (area : AreaRules)
    (g : Fraction → Fraction) (a b c : Fraction)
    (parts : Nat → Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0≤(g a).num) (hac : Fraction.le a c)
    (hcb : Fraction.lt c b) (hgc : 0<(g c).num)
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => gap g (parts m))) :
    EventuallyMutualRatiosOne (fun m => lowerSum g (parts m))
      (fun m => upperSum g (parts m)) := by
  obtain ⟨B,hB,N,hN⟩ := rectangle_interior_denominator_bound
    area g a b c parts hg hbase hac hcb hgc hgap
  apply varying_ratios_approach_one_eventually B hB _ _ N
    (fun m hm => (hN m hm).1) (fun m hm => (hN m hm).2)
  intro eps heps
  obtain ⟨K,hK⟩ := hgap eps heps
  refine ⟨K,fun m hm => ?_⟩
  have hnon := (gap_bound g (parts m) hg (maxWidth (parts m))
    (maxWidth_bounds (parts m)).1).1
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (Fraction.abs_of_nonnegative _ hnon)) (hK m hm)

end NewtonLimitDynamics.Polygon.RectangleContent
