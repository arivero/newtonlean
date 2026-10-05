import BarrowLib.Polygon.EquivalentDuration

/-! Calibrated actual coarse/two-half-cell accumulation. All maps are rational
point maps; sample/arrival bounds are explicit finite premises. -/

namespace NewtonLimitDynamics.Polygon.CalibratedRefinement
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates FiniteAccumulation

-- The local defect is calculated on the actual coarse map.
def localSource (tau h L E B V : Fraction) : Fraction :=
  Fraction.add (Fraction.mul (Fraction.mul h h).abs B)
    (Fraction.mul tau (Fraction.mul h.abs
      (Fraction.add
        (Fraction.add (Fraction.mul L (Fraction.mul h.abs V)) E)
        (Fraction.add (Fraction.mul L (Fraction.mul (Fraction.mul h h).abs B)) E))))

def blockSource (tau h L E B V : Fraction) (ht : 0 < tau.num) : Fraction :=
  Fraction.add
    (Fraction.add
      (Fraction.mul (TimeCalibration.amplification tau h L ht)
        (Fraction.mul (Fraction.mul tau h.abs) E))
      (Fraction.mul (Fraction.mul tau h.abs) E))
    (localSource tau h L E B V)

def blockFactor (tau h L : Fraction) (ht : 0 < tau.num) : Fraction :=
  Fraction.mul (TimeCalibration.amplification tau h L ht)
    (TimeCalibration.amplification tau h L ht)

theorem localSource_nonnegative (tau h L E B V : Fraction)
    (ht : 0 < tau.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hB : 0 ≤ B.num) (hV : 0 ≤ V.num) : 0 ≤ (localSource tau h L E B V).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative _) hB)
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht)
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
        (Fraction.nonnegative_add _ _
          (Fraction.nonnegative_add _ _
            (Fraction.nonnegative_mul _ _ hL
              (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h) hV)) hE)
          (Fraction.nonnegative_add _ _
            (Fraction.nonnegative_mul _ _ hL
              (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative _) hB)) hE))))

theorem blockSource_nonnegative (tau h L E B V : Fraction)
    (ht : 0 < tau.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hB : 0 ≤ B.num) (hV : 0 ≤ V.num) : 0 ≤ (blockSource tau h L E B V ht).num := by
  have hS : 0 ≤ (Fraction.mul (Fraction.mul tau h.abs) E).num :=
    Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) (Fraction.abs_num_nonnegative h)) hE
  exact Fraction.nonnegative_add _ _
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _ (TimeCalibration.amplification_nonnegative tau h L ht hL) hS) hS)
    (localSource_nonnegative tau h L E B V ht hL hE hB hV)

theorem twoHalf_local_error_at (tau : Fraction) (ht : 0 < tau.num)
    (b : Point → Point) (h L E B V : Fraction) (t : Point × Point)
    (hL : 0 ≤ L.num)
    (hfirst : Fraction.le
      (pointDistance (b (cell b h t).1) (b (oneFull b h t).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (cell b h t).1 (oneFull b h t).1)) E))
    (hsecond : Fraction.le
      (pointDistance (b (twoHalf b h t).1) (b (oneFull b h t).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (twoHalf b h t).1 (oneFull b h t).1)) E))
    (hB : Fraction.le (pointNorm (b (cell b h t).1)) B)
    (hV : Fraction.le (pointNorm t.2) V) :
    Fraction.le (TimeCalibration.distance tau (twoHalf b h t) (oneFull b h t))
      (localSource tau h L E B V) := by
  have hp := twoHalf_position_error b h B t hB
  have hv := twoHalf_velocity_error_closed_at b h L E B t hL hB hfirst hsecond
  have hvc := Fraction.add_le_add_right
    (Fraction.mul_le_mul_nonnegative_left
      (Fraction.mul_le_mul_nonnegative_left hV h.abs (Fraction.abs_num_nonnegative h)) L hL) E
  have hvel := Fraction.mul_le_mul_nonnegative_left
    (Fraction.add_le_add_right hvc
      (Fraction.add (Fraction.mul L (Fraction.mul (Fraction.mul h h).abs B)) E))
    h.abs (Fraction.abs_num_nonnegative h)
  exact Fraction.add_le_add hp
    (Fraction.mul_le_mul_nonnegative_left (Fraction.magnitudes.le_trans hv hvel)
      tau (Int.le_of_lt ht))

theorem twoHalf_local_error (tau : Fraction) (ht : 0 < tau.num)
    (b : Point → Point) (h L E B V : Fraction) (t : Point × Point)
    (hL : 0 ≤ L.num) (hlocal : comparisonContract b b L E)
    (hB : Fraction.le (pointNorm (b (cell b h t).1)) B)
    (hV : Fraction.le (pointNorm t.2) V) :
    Fraction.le (TimeCalibration.distance tau (twoHalf b h t) (oneFull b h t))
      (localSource tau h L E B V) :=
  twoHalf_local_error_at tau ht b h L E B V t hL
    (hlocal (cell b h t).1 (oneFull b h t).1)
    (hlocal (twoHalf b h t).1 (oneFull b h t).1) hB hV

/-- Only the four comparisons made by the actual paired block are needed. -/
structure BlockComparisons (a b : Point → Point) (h L E : Fraction)
    (s t : Point × Point) : Prop where
  firstCross : Fraction.le
    (pointDistance (a (cell a h s).1) (b (cell b h t).1))
    (Fraction.add (Fraction.mul L
      (pointDistance (cell a h s).1 (cell b h t).1)) E)
  secondCross : Fraction.le
    (pointDistance (a (twoHalf a h s).1) (b (twoHalf b h t).1))
    (Fraction.add (Fraction.mul L
      (pointDistance (twoHalf a h s).1 (twoHalf b h t).1)) E)
  firstLocal : Fraction.le
    (pointDistance (b (cell b h t).1) (b (oneFull b h t).1))
    (Fraction.add (Fraction.mul L
      (pointDistance (cell b h t).1 (oneFull b h t).1)) E)
  secondLocal : Fraction.le
    (pointDistance (b (twoHalf b h t).1) (b (oneFull b h t).1))
    (Fraction.add (Fraction.mul L
      (pointDistance (twoHalf b h t).1 (oneFull b h t).1)) E)

/-- Actual first and second fine-cell samples each contribute their own E. -/
theorem cross_block_error_at (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E B V : Fraction) (s t : Point × Point)
    (hL : 0 ≤ L.num) (hc : BlockComparisons a b h L E s t)
    (hB : Fraction.le (pointNorm (b (cell b h t).1)) B)
    (hV : Fraction.le (pointNorm t.2) V) :
    Fraction.le (TimeCalibration.distance tau (twoHalf a h s) (oneFull b h t))
      (Fraction.add
        (Fraction.mul (blockFactor tau h L ht) (TimeCalibration.distance tau s t))
        (blockSource tau h L E B V ht)) := by
  let K := TimeCalibration.amplification tau h L ht
  let S := Fraction.mul (Fraction.mul tau h.abs) E
  have hK := TimeCalibration.amplification_nonnegative tau h L ht hL
  have h1 := TimeCalibration.cell_amplification_at tau ht a b h L E s t hL hc.firstCross
  have h2 := TimeCalibration.cell_amplification_at tau ht a b h L E
    (cell a h s) (cell b h t) hL hc.secondCross
  have hprop := Fraction.magnitudes.le_trans h2
    (Fraction.add_le_add_right (Fraction.mul_le_mul_nonnegative_left h1 K hK) S)
  have hl := twoHalf_local_error_at tau ht b h L E B V t hL
    hc.firstLocal hc.secondLocal hB hV
  have htri := TimeCalibration.distance_triangle tau ht
    (twoHalf a h s) (twoHalf b h t) (oneFull b h t)
  apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans htri (Fraction.add_le_add hprop hl))
  simp only [K,S,blockFactor,blockSource,Fraction.equiv,Fraction.add,Fraction.mul,
    Int.add_mul,Int.mul_add]
  ac_nf

theorem cross_block_error (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E B V : Fraction) (s t : Point × Point)
    (hL : 0 ≤ L.num) (hcross : comparisonContract a b L E)
    (hlocal : comparisonContract b b L E)
    (hB : Fraction.le (pointNorm (b (cell b h t).1)) B)
    (hV : Fraction.le (pointNorm t.2) V) :
    Fraction.le (TimeCalibration.distance tau (twoHalf a h s) (oneFull b h t))
      (Fraction.add
        (Fraction.mul (blockFactor tau h L ht) (TimeCalibration.distance tau s t))
        (blockSource tau h L E B V ht)) :=
  cross_block_error_at tau ht a b h L E B V s t hL
    ⟨hcross (cell a h s).1 (cell b h t).1,
      hcross (twoHalf a h s).1 (twoHalf b h t).1,
      hlocal (cell b h t).1 (oneFull b h t).1,
      hlocal (twoHalf b h t).1 (oneFull b h t).1⟩ hB hV

theorem actual_error_le_source_at (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E B V : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) :
    (n : Nat) →
    (hc : ∀ k, k < n → BlockComparisons a b h L E
      (fineAt a h s k) (coarseAt b h s k)) →
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (b (cell b h (coarseAt b h s k)).1)) B) →
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt b h s k).2) V) →
    Fraction.le (TimeCalibration.distance tau (fineAt a h s n) (coarseAt b h s n))
      (FiniteRecurrence.sourceBudget (blockFactor tau h L ht)
        (blockSource tau h L E B V ht) n)
  | 0, _, _, _ => Fraction.le_of_equiv (TimeCalibration.distance_self_zero tau s)
  | n+1, hc, hB, hV => by
      have hs := cross_block_error_at tau ht a b h L E B V
        (fineAt a h s n) (coarseAt b h s n) hL (hc n (by omega))
        (hB n (by omega)) (hV n (by omega))
      have hi := actual_error_le_source_at tau ht a b h L E B V s hL n
        (fun k hk => hc k (by omega))
        (fun k hk => hB k (by omega)) (fun k hk => hV k (by omega))
      have hK := TimeCalibration.amplification_nonnegative tau h L ht hL
      exact Fraction.magnitudes.le_trans hs
        (Fraction.add_le_add_right
          (Fraction.mul_le_mul_nonnegative_left hi (blockFactor tau h L ht)
            (Fraction.nonnegative_mul _ _ hK hK)) (blockSource tau h L E B V ht))

theorem actual_error_le_source (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E B V : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hcross : comparisonContract a b L E)
    (hlocal : comparisonContract b b L E) :
    (n : Nat) →
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (b (cell b h (coarseAt b h s k)).1)) B) →
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt b h s k).2) V) →
    Fraction.le (TimeCalibration.distance tau (fineAt a h s n) (coarseAt b h s n))
      (FiniteRecurrence.sourceBudget (blockFactor tau h L ht)
        (blockSource tau h L E B V ht) n) :=
  fun n hB hV => actual_error_le_source_at tau ht a b h L E B V s hL n
    (fun k _ =>
      ⟨hcross (cell a h (fineAt a h s k)).1 (cell b h (coarseAt b h s k)).1,
       hcross (twoHalf a h (fineAt a h s k)).1
         (twoHalf b h (coarseAt b h s k)).1,
       hlocal (cell b h (coarseAt b h s k)).1
         (oneFull b h (coarseAt b h s k)).1,
       hlocal (twoHalf b h (coarseAt b h s k)).1
         (oneFull b h (coarseAt b h s k)).1⟩) hB hV

theorem actual_uniform_error_at (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E B V : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hB0 : 0 ≤ B.num) (hV0 : 0 ≤ V.num)
    (n : Nat) (hs : TimeCalibration.Window tau h L ht (2*n))
    (hc : ∀ k, k < n → BlockComparisons a b h L E
      (fineAt a h s k) (coarseAt b h s k))
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (b (cell b h (coarseAt b h s k)).1)) B)
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt b h s k).2) V) :
    Fraction.le (TimeCalibration.distance tau (fineAt a h s n) (coarseAt b h s n))
      (Fraction.mul (Fraction.ofInt (2*(n : Int))) (blockSource tau h L E B V ht)) := by
  let K := TimeCalibration.amplification tau h L ht
  let R := blockFactor tau h L ht
  let S := blockSource tau h L E B V ht
  have hK := TimeCalibration.amplification_nonnegative tau h L ht hL
  have hR : 0 ≤ R.num := Fraction.nonnegative_mul _ _ hK hK
  have hS := blockSource_nonnegative tau h L E B V ht hL hE hB0 hV0
  have hone : Fraction.le (Fraction.ofInt 1) R := by
    have hb := TimeCalibration.one_le_amplification tau h L ht hL
    have hm := Fraction.mul_le_mul_nonnegative_left hb K hK
    have h1 : Fraction.le (Fraction.ofInt 1) (Fraction.mul K (Fraction.ofInt 1)) :=
      Fraction.le_equiv_right hb (by
        simp only [K,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one])
    exact Fraction.magnitudes.le_trans h1 hm
  have hp := Fraction.le_equiv_left (FiniteFactorProducts.fpower_square K n)
    (TimeCalibration.amplification_power_le_two tau h L ht hL (2*n) hs)
  exact Fraction.magnitudes.le_trans
    (actual_error_le_source_at tau ht a b h L E B V s hL n hc hB hV)
    (FiniteRecurrence.sourceBudget_two_count R S n hR hS hone hp)

theorem actual_uniform_error (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E B V : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hB0 : 0 ≤ B.num) (hV0 : 0 ≤ V.num)
    (hcross : comparisonContract a b L E) (hlocal : comparisonContract b b L E)
    (n : Nat) (hs : TimeCalibration.Window tau h L ht (2*n))
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (b (cell b h (coarseAt b h s k)).1)) B)
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt b h s k).2) V) :
    Fraction.le (TimeCalibration.distance tau (fineAt a h s n) (coarseAt b h s n))
      (Fraction.mul (Fraction.ofInt (2*(n : Int))) (blockSource tau h L E B V ht)) :=
  actual_uniform_error_at tau ht a b h L E B V s hL hE hB0 hV0 n hs
    (fun k _ =>
      ⟨hcross (cell a h (fineAt a h s k)).1 (cell b h (coarseAt b h s k)).1,
       hcross (twoHalf a h (fineAt a h s k)).1
         (twoHalf b h (coarseAt b h s k)).1,
       hlocal (cell b h (coarseAt b h s k)).1
         (oneFull b h (coarseAt b h s k)).1,
       hlocal (twoHalf b h (coarseAt b h s k)).1
         (oneFull b h (coarseAt b h s k)).1⟩) hB hV

def consistencyCoefficient (tau T L B V : Fraction) : Fraction :=
  Fraction.add B (Fraction.mul (Fraction.mul tau L) (Fraction.add V (Fraction.mul T B)))

/-- An actual block source is O(h²)+O(hE), with a mesh-independent coefficient. -/
theorem blockSource_bound (tau : Fraction) (ht : 0 < tau.num)
    (h T L E B V : Fraction) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hB : 0 ≤ B.num) (hHT : Fraction.le h.abs T)
    (hK : Fraction.le (TimeCalibration.amplification tau h L ht) (Fraction.ofInt 2)) :
    Fraction.le (blockSource tau h L E B V ht)
      (Fraction.add
        (Fraction.mul (Fraction.mul h.abs h.abs) (consistencyCoefficient tau T L B V))
        (Fraction.mul (Fraction.ofInt 5) (Fraction.mul (Fraction.mul tau h.abs) E))) := by
  let H := h.abs
  let S := Fraction.mul (Fraction.mul tau H) E
  have hS : 0 ≤ S.num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) (Fraction.abs_num_nonnegative h)) hE
  have hprop := Fraction.add_le_add_right
    (Fraction.mul_le_mul_nonnegative hK S hS) S
  have hsq := Fraction.abs_mul h h
  have hb := Fraction.le_equiv_left (Fraction.mul_equiv hsq (Fraction.equiv_refl B))
    (Fraction.mul_le_mul_nonnegative
      (Fraction.mul_le_mul_nonnegative_left hHT H (Fraction.abs_num_nonnegative h)) B hB)
  have hinner := Fraction.add_le_add_left
    (Fraction.add_le_add_right (Fraction.mul_le_mul_nonnegative_left hb L hL) E)
    (Fraction.add (Fraction.mul L (Fraction.mul H V)) E)
  have hvel := Fraction.mul_le_mul_nonnegative_left
    (Fraction.mul_le_mul_nonnegative_left hinner H (Fraction.abs_num_nonnegative h))
    tau (Int.le_of_lt ht)
  have hlocal := Fraction.add_le_add_left hvel (Fraction.mul (Fraction.mul h h).abs B)
  have hsum := Fraction.add_le_add hprop hlocal
  let W := Fraction.mul tau (Fraction.mul H
    (Fraction.add (Fraction.add (Fraction.mul L (Fraction.mul H V)) E)
      (Fraction.add (Fraction.mul L (Fraction.mul (Fraction.mul H T) B)) E)))
  have he : Fraction.equiv
      (Fraction.add (Fraction.add (Fraction.mul (Fraction.ofInt 2) S) S)
        (Fraction.add (Fraction.mul (Fraction.mul h h).abs B) W))
      (Fraction.add (Fraction.add (Fraction.mul (Fraction.ofInt 2) S) S)
        (Fraction.add (Fraction.mul (Fraction.mul H H) B) W)) :=
    Fraction.add_equiv (Fraction.equiv_refl _)
      (Fraction.add_equiv (Fraction.mul_equiv hsq (Fraction.equiv_refl B))
        (Fraction.equiv_refl W))
  apply Fraction.le_equiv_right (Fraction.le_equiv_right hsum he)
  simp only [S,W,H,consistencyCoefficient,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    show (5 : Int) = 2+1+1+1 by rfl,
    Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

theorem coarseAt_eq_run (a : Point → Point) (h : Fraction) (s : Point × Point) :
    (n : Nat) → coarseAt a h s n = BoundedIteration.run a (Fraction.add h h) s n
  | 0 => rfl
  | n+1 => congrArg (oneFull a h) (coarseAt_eq_run a h s n)

theorem fineAt_eq_run (a : Point → Point) (h : Fraction) (s : Point × Point) :
    (n : Nat) → fineAt a h s n = BoundedIteration.run a h s (2*n)
  | 0 => rfl
  | n+1 => by
      simp only [Nat.mul_succ,Nat.add_succ,Nat.add_zero,BoundedIteration.run,fineAt,twoHalf]
      rw [fineAt_eq_run a h s n]

end NewtonLimitDynamics.Polygon.CalibratedRefinement
