import BarrowLib.Polygon.FiniteFactorProducts
import BarrowLib.Polygon.FiniteEstimates
import BarrowLib.Common.FiniteGrowth
import BarrowLib.Common.FinitePowers

/-!
Finite accumulation for actual coarse cells and pairs of half cells. The point
map is arbitrary; applications to Newtonian central fields impose centrality
separately. All estimates are coordinate L1 estimates on rational states.
-/

namespace NewtonLimitDynamics.Polygon.FiniteAccumulation

open NewtonLimitDynamics
open TimeSubdivision
open PointBounds
open FiniteEstimates

/-- Iterates of the actual full-cell and two-half-cell maps. -/
def coarseAt (a : Point → Point) (h : Fraction) (s : Point × Point) : Nat → Point × Point
  | 0 => s
  | n + 1 => oneFull a h (coarseAt a h s n)

def fineAt (a : Point → Point) (h : Fraction) (s : Point × Point) : Nat → Point × Point
  | 0 => s
  | n + 1 => twoHalf a h (fineAt a h s n)

/-- One application of the two-half-cell perturbation bound. -/
def twoStepBudget (h L E D : Fraction) : Fraction :=
  Fraction.add
    (Fraction.mul (amplification L h)
      (Fraction.add (Fraction.mul (amplification L h) D)
        (Fraction.mul h.abs E)))
    (Fraction.mul h.abs E)

/-- The actual local mismatch, using the bounded first-half sample and the
coarse starting velocity. No adjacent-error hypothesis is hidden here. -/
def localBudget (h L E B : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add
    (Fraction.mul (Fraction.mul h h).abs B)
    (Fraction.mul h.abs
      (Fraction.add
        (Fraction.add (Fraction.mul L
          (Fraction.mul h.abs (pointNorm s.2))) E)
        (Fraction.add (Fraction.mul L
          (Fraction.mul (Fraction.mul h h).abs B)) E)))

/-- Replace the actual coarse velocity in the local source by a uniform
bound `V`. This is a separate confinement premise for the iterated result. -/
def uniformLocalBudget (h L E B V : Fraction) : Fraction :=
  Fraction.add
    (Fraction.mul (Fraction.mul h h).abs B)
    (Fraction.mul h.abs
      (Fraction.add
        (Fraction.add (Fraction.mul L (Fraction.mul h.abs V)) E)
        (Fraction.add (Fraction.mul L
          (Fraction.mul (Fraction.mul h h).abs B)) E)))

theorem localBudget_le_uniform (h L E B V : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hV : Fraction.le (pointNorm s.2) V) :
    Fraction.le (localBudget h L E B s) (uniformLocalBudget h L E B V) := by
  have h₁ := Fraction.mul_le_mul_nonnegative_left hV h.abs
    (Fraction.abs_num_nonnegative h)
  have h₂ := Fraction.mul_le_mul_nonnegative_left h₁ L hL
  have h₃ := Fraction.add_le_add_right h₂ E
  have h₄ := Fraction.add_le_add_right h₃
    (Fraction.add (Fraction.mul L
      (Fraction.mul (Fraction.mul h h).abs B)) E)
  have h₅ := Fraction.mul_le_mul_nonnegative_left h₄ h.abs
    (Fraction.abs_num_nonnegative h)
  exact Fraction.add_le_add_left h₅
    (Fraction.mul (Fraction.mul h h).abs B)

/-- The constant source per block includes both half-cell sampling errors. -/
def uniformBlockSource (h L E B V : Fraction) : Fraction :=
  Fraction.add
    (Fraction.add
      (Fraction.mul (amplification L h) (Fraction.mul h.abs E))
      (Fraction.mul h.abs E))
    (uniformLocalBudget h L E B V)

/-- The same recurrence with a constant source, once every actual coarse
state has velocity bounded by `V`. -/
def constantErrorBudget (h L E B V : Fraction) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | n + 1 => Fraction.add
      (Fraction.mul (amplification L h)
        (Fraction.mul (amplification L h)
          (constantErrorBudget h L E B V n)))
      (uniformBlockSource h L E B V)

def blockFactor (h L : Fraction) : Fraction :=
  Fraction.mul (amplification L h) (amplification L h)

/-- Core scalar powers; no representative enters an actual state recurrence. -/
def factorPower (r : Rat) (n : Nat) : Rat := r ^ n

def count (n : Nat) : Fraction := Fraction.ofInt (n : Int)

theorem amplification_nonnegative (h L : Fraction) (hL : 0 ≤ L.num) :
    0 ≤ (amplification L h).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_add _ _ (by decide) (Fraction.abs_num_nonnegative h))
    (Fraction.nonnegative_add _ _ (by decide)
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
        hL))

private theorem one_le_one_add (a : Fraction) (ha : 0 ≤ a.num) :
    Fraction.le (Fraction.ofInt 1) (Fraction.add (Fraction.ofInt 1) a) := by
  unfold Fraction.le Fraction.add Fraction.ofInt
  dsimp
  have hp := Int.le_of_lt a.den_pos
  omega

theorem one_le_amplification (h L : Fraction) (hL : 0 ≤ L.num) :
    Fraction.le (Fraction.ofInt 1) (amplification L h) := by
  let u := Fraction.add (Fraction.ofInt 1) h.abs
  let v := Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs L)
  have hu := one_le_one_add h.abs (Fraction.abs_num_nonnegative h)
  have hv := one_le_one_add (Fraction.mul h.abs L)
    (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h) hL)
  have h₁ := Fraction.mul_le_mul_nonnegative hu (Fraction.ofInt 1) (by decide)
  have h₂ := Fraction.mul_le_mul_nonnegative_left hv u (by
    unfold u Fraction.add Fraction.ofInt
    dsimp
    have hp := h.abs.den_pos
    have hn := Fraction.abs_num_nonnegative h
    omega)
  have hc := Fraction.magnitudes.le_trans h₁ h₂
  apply Fraction.le_equiv_left (by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    decide) hc

theorem blockFactor_nonnegative (h L : Fraction) (hL : 0 ≤ L.num) :
    0 ≤ (blockFactor h L).num :=
  Fraction.nonnegative_mul _ _
    (amplification_nonnegative h L hL) (amplification_nonnegative h L hL)

theorem one_le_blockFactor (h L : Fraction) (hL : 0 ≤ L.num) :
    Fraction.le (Fraction.ofInt 1) (blockFactor h L) := by
  have hk := one_le_amplification h L hL
  have h₁ := Fraction.mul_le_mul_nonnegative hk (Fraction.ofInt 1) (by decide)
  have h₂ := Fraction.mul_le_mul_nonnegative_left hk (amplification L h)
    (amplification_nonnegative h L hL)
  have hc := Fraction.magnitudes.le_trans h₁ h₂
  apply Fraction.le_equiv_left (by
    simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt]
    decide) hc

theorem uniformBlockSource_nonnegative (h L E B V : Fraction)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hB : 0 ≤ B.num) (hV : 0 ≤ V.num) :
    0 ≤ (uniformBlockSource h L E B V).num := by
  unfold uniformBlockSource uniformLocalBudget
  apply Fraction.nonnegative_add
  · apply Fraction.nonnegative_add
    · exact Fraction.nonnegative_mul _ _ (amplification_nonnegative h L hL)
        (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h) hE)
    · exact Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h) hE
  · apply Fraction.nonnegative_add
    · exact Fraction.nonnegative_mul _ _
        (Fraction.abs_num_nonnegative (Fraction.mul h h)) hB
    · apply Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
      apply Fraction.nonnegative_add
      · apply Fraction.nonnegative_add
        · exact Fraction.nonnegative_mul _ _ hL
            (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h) hV)
        · exact hE
      · apply Fraction.nonnegative_add
        · exact Fraction.nonnegative_mul _ _ hL
            (Fraction.nonnegative_mul _ _
              (Fraction.abs_num_nonnegative (Fraction.mul h h)) hB)
        · exact hE

/-- Propagation through two actual half cells with distinct sample maps.
Each application contributes its own `hE` term. -/
theorem cross_twoHalf_perturbation (a b : Point → Point) (h L E : Fraction)
    (s t : Point × Point) (hL : 0 ≤ L.num)
    (hc : comparisonContract a b L E) :
    Fraction.le (stateDistance (twoHalf a h s) (twoHalf b h t))
      (twoStepBudget h L E (stateDistance s t)) := by
  have h₁ := cell_amplification a b h L E (cell a h s) (cell b h t) hL hc
  have h₂ := cell_amplification a b h L E s t hL hc
  have hm := Fraction.mul_le_mul_nonnegative_left h₂ (amplification L h)
    (amplification_nonnegative h L hL)
  have hs := Fraction.add_le_add_right hm (Fraction.mul h.abs E)
  exact Fraction.magnitudes.le_trans h₁ hs

/-- The same-map public theorem is a cross-map instance. -/
theorem twoHalf_perturbation (a : Point → Point) (h L E : Fraction)
    (s t : Point × Point) (hL : 0 ≤ L.num)
    (hc : comparisonContract a a L E) :
    Fraction.le (stateDistance (twoHalf a h s) (twoHalf a h t))
      (twoStepBudget h L E (stateDistance s t)) :=
  cross_twoHalf_perturbation a a h L E s t hL hc

/-- One actual cross-map block. The local defect uses the coarse map `b`,
while propagation of the distinct fine map `a` uses the cross contract. -/
theorem cross_block_error (a b : Point → Point) (h L E B : Fraction)
    (s t : Point × Point) (hL : 0 ≤ L.num)
    (hcross : comparisonContract a b L E)
    (hlocal : comparisonContract b b L E)
    (hB : Fraction.le (pointNorm (b (cell b h t).1)) B) :
    Fraction.le (stateDistance (twoHalf a h s) (oneFull b h t))
      (Fraction.add (twoStepBudget h L E (stateDistance s t))
        (localBudget h L E B t)) := by
  have ht := stateDistance_triangle (twoHalf a h s) (twoHalf b h t)
    (oneFull b h t)
  have hp := cross_twoHalf_perturbation a b h L E s t hL hcross
  have hl := twoHalf_state_error_closed b h L E B t hL hB hlocal
  exact Fraction.magnitudes.le_trans ht (Fraction.add_le_add hp hl)

theorem block_error (a : Point → Point) (h L E B : Fraction)
    (s t : Point × Point) (hL : 0 ≤ L.num)
    (hc : comparisonContract a a L E)
    (hB : Fraction.le (pointNorm (a (cell a h t).1)) B) :
    Fraction.le (stateDistance (twoHalf a h s) (oneFull a h t))
      (Fraction.add (twoStepBudget h L E (stateDistance s t))
        (localBudget h L E B t)) :=
  cross_block_error a a h L E B s t hL hc hc hB

/-- The budget is a finite rational recurrence whose local source is
calculated at each actual coarse state. -/
def errorBudget (a : Point → Point) (h L E B : Fraction)
    (s : Point × Point) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | n + 1 => Fraction.add
      (twoStepBudget h L E (errorBudget a h L E B s n))
      (localBudget h L E B (coarseAt a h s n))

/-- Finite accumulation of distinct fine/coarse sample maps. The local
source is calculated at actual coarse states of `b`; the cross contract
propagates the fine-versus-coarse separation. -/
theorem cross_actual_error_le_budget (a b : Point → Point) (h L E B : Fraction)
    (s : Point × Point) (hL : 0 ≤ L.num)
    (hcross : comparisonContract a b L E)
    (hlocal : comparisonContract b b L E) :
    (n : Nat) →
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (b (cell b h (coarseAt b h s k)).1)) B) →
      Fraction.le (stateDistance (fineAt a h s n) (coarseAt b h s n))
        (errorBudget b h L E B s n)
  | 0, _ => Fraction.le_of_equiv (stateDistance_self_zero s)
  | n + 1, hB => by
      have hs := cross_block_error a b h L E B (fineAt a h s n)
        (coarseAt b h s n) hL hcross hlocal (hB n (Nat.lt_succ_self n))
      have hi := cross_actual_error_le_budget a b h L E B s hL hcross hlocal n
        (fun k hk => hB k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      have hm := Fraction.mul_le_mul_nonnegative_left hi (amplification L h)
        (amplification_nonnegative h L hL)
      have ha := Fraction.add_le_add_right hm (Fraction.mul h.abs E)
      have hm₂ := Fraction.mul_le_mul_nonnegative_left ha (amplification L h)
        (amplification_nonnegative h L hL)
      have hb := Fraction.add_le_add_right hm₂ (Fraction.mul h.abs E)
      have hf := Fraction.add_le_add_right hb
        (localBudget h L E B (coarseAt b h s n))
      exact Fraction.magnitudes.le_trans hs hf

/-- Same-map compatibility instance of the cross-map recurrence. -/
theorem actual_error_le_budget (a : Point → Point) (h L E B : Fraction)
    (s : Point × Point) (hL : 0 ≤ L.num)
    (hc : comparisonContract a a L E) :
    (n : Nat) →
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (a (cell a h (coarseAt a h s k)).1)) B) →
      Fraction.le (stateDistance (fineAt a h s n) (coarseAt a h s n))
        (errorBudget a h L E B s n) :=
  cross_actual_error_le_budget a a h L E B s hL hc hc

theorem errorBudget_le_constant (a : Point → Point)
    (h L E B V : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) :
    (n : Nat) →
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt a h s k).2) V) →
      Fraction.le (errorBudget a h L E B s n)
        (constantErrorBudget h L E B V n)
  | 0, _ => Fraction.magnitudes.le_refl _
  | n + 1, hV => by
      have hi := errorBudget_le_constant a h L E B V s hL n
        (fun k hk => hV k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      have hK := amplification_nonnegative h L hL
      have h₁ := Fraction.mul_le_mul_nonnegative_left hi (amplification L h) hK
      have h₂ := Fraction.add_le_add_right h₁ (Fraction.mul h.abs E)
      have h₃ := Fraction.mul_le_mul_nonnegative_left h₂ (amplification L h) hK
      have h₄ := Fraction.add_le_add_right h₃ (Fraction.mul h.abs E)
      have h₅ := localBudget_le_uniform h L E B V (coarseAt a h s n) hL
        (hV n (Nat.lt_succ_self n))
      have hs := Fraction.add_le_add h₄ h₅
      apply Fraction.le_equiv_right hs
      simp only [errorBudget, twoStepBudget, constantErrorBudget,
        uniformBlockSource, Fraction.equiv, Fraction.add, Fraction.mul]
      simp only [Int.add_mul, Int.mul_add]
      ac_nf

/-- Finite-prefix coarse velocity confinement converts the cross-map error
into the same constant rational recurrence. -/
theorem cross_actual_error_le_constant_budget (a b : Point → Point)
    (h L E B V : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num)
    (hcross : comparisonContract a b L E)
    (hlocal : comparisonContract b b L E)
    (n : Nat)
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (b (cell b h (coarseAt b h s k)).1)) B)
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt b h s k).2) V) :
    Fraction.le (stateDistance (fineAt a h s n) (coarseAt b h s n))
      (constantErrorBudget h L E B V n) :=
  Fraction.magnitudes.le_trans
    (cross_actual_error_le_budget a b h L E B s hL hcross hlocal n hB)
    (errorBudget_le_constant b h L E B V s hL n hV)

theorem actual_error_le_constant_budget (a : Point → Point)
    (h L E B V : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num)
    (hc : comparisonContract a a L E)
    (n : Nat)
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (a (cell a h (coarseAt a h s k)).1)) B)
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt a h s k).2) V) :
    Fraction.le (stateDistance (fineAt a h s n) (coarseAt a h s n))
      (constantErrorBudget h L E B V n) :=
  cross_actual_error_le_constant_budget a a h L E B V s hL hc hc n hB hV

/-- A constant-source recurrence is bounded by its finite amplification
power. Project derivation (Sol 6.1, 10 October 2026), with its exact statement
and finite induction as provenance; no historical textual attribution.
Only scalar bounds cross the temporary bridge. Actual states are unchanged. -/
theorem constant_budget_power_bound (h L E B V : Fraction)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hB : 0 ≤ B.num) (hV : 0 ≤ V.num) :
    (n : Nat) →
      (constantErrorBudget h L E B V n).toRat ≤
        (n : Rat) * (uniformBlockSource h L E B V).toRat *
          factorPower (blockFactor h L).toRat n
  | 0 => by
      simp [constantErrorBudget, Fraction.toRat_ofInt]
  | n + 1 => by
      let r := (blockFactor h L).toRat
      let C := (uniformBlockSource h L E B V).toRat
      have hi := constant_budget_power_bound h L E B V hL hE hB hV n
      have hr : 0 ≤ r := (Fraction.nonnegative_iff_toRat _).mp
        (blockFactor_nonnegative h L hL)
      have hC : 0 ≤ C := (Fraction.nonnegative_iff_toRat _).mp
        (uniformBlockSource_nonnegative h L E B V hL hE hB hV)
      have h1 : 1 ≤ r := by
        simpa only [Fraction.toRat_ofInt, Rat.intCast_one] using
          (Fraction.le_iff_toRat _ _).mp (one_le_blockFactor h L hL)
      have hm := Rat.mul_le_mul_of_nonneg_left hi hr
      have hc := Rat.mul_le_mul_of_nonneg_left
        (FinitePowers.one_le_power r hr h1 (n + 1)) hC
      simp only [constantErrorBudget, Fraction.toRat_add, Fraction.toRat_mul,
        factorPower, Rat.pow_succ]
      change _ ≤ ((n + 1 : Nat) : Rat) * C * (r ^ n * r)
      change r * (constantErrorBudget h L E B V n).toRat ≤
        r * ((n : Rat) * C * r ^ n) at hm
      simp only [factorPower, Rat.pow_succ] at hc
      simp only [r, C, blockFactor, Fraction.toRat_mul] at hm hc ⊢
      grind

/-- Cross-map mesh-uniform form conditional on the finite power bound. -/
theorem cross_actual_error_le_two_count_source (a b : Point → Point)
    (h L E B V : Fraction) (s : Point × Point) (n : Nat)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hBnonneg : 0 ≤ B.num) (hVnonneg : 0 ≤ V.num)
    (hcross : comparisonContract a b L E)
    (hlocal : comparisonContract b b L E)
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (b (cell b h (coarseAt b h s k)).1)) B)
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt b h s k).2) V)
    (hpower : factorPower (blockFactor h L).toRat n ≤ 2) :
    Fraction.le (stateDistance (fineAt a h s n) (coarseAt b h s n))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (count n) (uniformBlockSource h L E B V))) := by
  have h₀ := cross_actual_error_le_constant_budget a b h L E B V s hL
    hcross hlocal n hB hV
  have h₁ := constant_budget_power_bound h L E B V hL hE hBnonneg hVnonneg n
  have hC := (Fraction.nonnegative_iff_toRat _).mp
    (uniformBlockSource_nonnegative h L E B V hL hE hBnonneg hVnonneg)
  have h₂ := Rat.mul_le_mul_of_nonneg_left hpower hC
  have h₃ := Rat.mul_le_mul_of_nonneg_left h₂ (Rat.natCast_nonneg (a := n))
  apply (Fraction.le_iff_toRat _ _).mpr
  have h₀' := (Fraction.le_iff_toRat _ _).mp h₀
  simp only [Fraction.toRat_mul, Fraction.toRat_ofInt, count,
    Rat.intCast_natCast, Rat.intCast_ofNat]
  grind

theorem actual_error_le_two_count_source (a : Point → Point)
    (h L E B V : Fraction) (s : Point × Point) (n : Nat)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hBnonneg : 0 ≤ B.num) (hVnonneg : 0 ≤ V.num)
    (hc : comparisonContract a a L E)
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (a (cell a h (coarseAt a h s k)).1)) B)
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt a h s k).2) V)
    (hpower : factorPower (blockFactor h L).toRat n ≤ 2) :
    Fraction.le (stateDistance (fineAt a h s n) (coarseAt a h s n))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (count n) (uniformBlockSource h L E B V))) :=
  cross_actual_error_le_two_count_source a a h L E B V s n hL hE hBnonneg
    hVnonneg hc hc hB hV hpower

/-- The represented elapsed duration of `n` full cells, each of size `2h`. -/
def totalTime (h : Fraction) (n : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt (2 * (n : Int))) h

def SmallWindow (h L : Fraction) (n : Nat) : Prop :=
  Fraction.le
    (Fraction.mul (totalTime h n) (Fraction.add (Fraction.ofInt 1) L))
    ⟨1, 2, by decide⟩

/-- The old unit-gauge window is an instance of the shared dimensionless
pair-factor estimate, with two fine cells in each coarse block. -/
theorem blockFactor_power_le_two (h L : Fraction) (n : Nat)
    (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hs : SmallWindow h L n) :
    factorPower (blockFactor h L).toRat n ≤ 2 := by
  have hsmall : Fraction.le
      (Fraction.mul (Fraction.ofInt ((2*n : Nat) : Int))
        (Fraction.add h (Fraction.mul h L))) ⟨1,2,by decide⟩ := by
    apply Fraction.le_equiv_left (b := Fraction.mul (totalTime h n)
      (Fraction.add (Fraction.ofInt 1) L)) _ hs
    simp only [totalTime,Fraction.equiv,Fraction.mul,Fraction.add,Fraction.ofInt,
      Int.natCast_mul,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  have hb := FiniteFactorProducts.repeated_pair_le_two h (Fraction.mul h L) (2*n)
    hh (Fraction.nonnegative_mul _ _ hh hL) hsmall
  have hcoeff : Fraction.equiv (amplification L h)
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) h)
        (Fraction.add (Fraction.ofInt 1) (Fraction.mul h L))) :=
    Fraction.mul_equiv
      (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.abs_of_nonnegative h hh))
      (Fraction.add_equiv (Fraction.equiv_refl _)
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl L)))
  have he := (Fraction.equiv_iff_toRat _ _).mp
    (Fraction.equiv_trans (FiniteFactorProducts.fpower_square (amplification L h) n)
      (FiniteFactorProducts.fpower_congr hcoeff (2*n)))
  change (blockFactor h L).toRat ^ n ≤ 2
  rw [← HarmonicAccumulation.toRat_fpower]
  change (HarmonicAccumulation.fpower
    (Fraction.mul (amplification L h) (amplification L h)) n).toRat ≤ 2
  rw [he]
  simpa only [Fraction.toRat_ofInt, Rat.intCast_ofNat] using
    (Fraction.le_iff_toRat _ _).mp hb

/-- Uniform finite cross-map comparison of actual polygon endpoints on a
small window. `B` and `V` refer to the coarse map `b` on the finite prefix;
the cross contract covers counterfactual fine/coarse sample locations. -/
theorem cross_actual_uniform_error (a b : Point → Point) (h L E B V : Fraction)
    (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hBnonneg : 0 ≤ B.num) (hVnonneg : 0 ≤ V.num)
    (hs : SmallWindow h L n)
    (hcross : comparisonContract a b L E)
    (hlocal : comparisonContract b b L E)
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (b (cell b h (coarseAt b h s k)).1)) B)
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt b h s k).2) V) :
    Fraction.le (stateDistance (fineAt a h s n) (coarseAt b h s n))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (count n) (uniformBlockSource h L E B V))) :=
  cross_actual_error_le_two_count_source a b h L E B V s n hL hE
    hBnonneg hVnonneg hcross hlocal hB hV
    (blockFactor_power_le_two h L n hh hL hs)

/-- Same-map public theorem, retained as a cross-map instance. -/
theorem actual_uniform_error (a : Point → Point) (h L E B V : Fraction)
    (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hBnonneg : 0 ≤ B.num) (hVnonneg : 0 ≤ V.num)
    (hs : SmallWindow h L n)
    (hc : comparisonContract a a L E)
    (hB : ∀ k, k < n → Fraction.le
      (pointNorm (a (cell a h (coarseAt a h s k)).1)) B)
    (hV : ∀ k, k < n → Fraction.le (pointNorm (coarseAt a h s k).2) V) :
    Fraction.le (stateDistance (fineAt a h s n) (coarseAt a h s n))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (count n) (uniformBlockSource h L E B V))) :=
  cross_actual_uniform_error a a h L E B V s n hh hL hE hBnonneg hVnonneg
    hs hc hc hB hV

private def sampleZero : Fraction := Fraction.ofInt 0
private def sampleHalf : Fraction := ⟨1, 2, by decide⟩
private def sampleQuarter : Fraction := ⟨1, 4, by decide⟩
private def sampleState : Point × Point :=
  ((sampleZero, sampleZero), (sampleZero, sampleZero))
private def sampleDown : Point → Point :=
  fun _ => (sampleZero, Fraction.ofInt (-1))
private def sampleDownTwo : Point → Point :=
  fun _ => (sampleZero, Fraction.ofInt (-2))
private def sampleFiveQuarters : Fraction := ⟨5, 4, by decide⟩

/-- Two unequal constant maps satisfy a cross contract with `L=0, E=1`;
the coarse map also satisfies its local contract with the same upper error. -/
theorem cross_constant_contract :
    comparisonContract sampleDown sampleDownTwo sampleZero (Fraction.ofInt 1) := by
  intro p q
  have hz : Fraction.equiv (Fraction.mul sampleZero (pointDistance p q)) sampleZero := by
    simp only [sampleZero, Fraction.equiv, Fraction.mul, Fraction.ofInt]
    simp
  have hr : Fraction.equiv
      (Fraction.add (Fraction.mul sampleZero (pointDistance p q)) (Fraction.ofInt 1))
      (Fraction.ofInt 1) :=
    Fraction.equiv_trans (Fraction.add_equiv hz (Fraction.equiv_refl _)) (by decide)
  have hl : Fraction.le (pointDistance (sampleDown p) (sampleDownTwo q))
      (Fraction.ofInt 1) := by
    unfold sampleDown sampleDownTwo pointDistance pointNorm pointSub pointNeg
      pointAdd Fraction.le Fraction.add Fraction.abs Fraction.ofInt sampleZero
    decide
  exact Fraction.le_equiv_right hl (Fraction.equiv_symm hr)

theorem coarse_constant_contract :
    comparisonContract sampleDownTwo sampleDownTwo sampleZero (Fraction.ofInt 1) := by
  intro p q
  have hz : Fraction.equiv (Fraction.mul sampleZero (pointDistance p q)) sampleZero := by
    simp only [sampleZero, Fraction.equiv, Fraction.mul, Fraction.ofInt]
    simp
  have hr : Fraction.equiv
      (Fraction.add (Fraction.mul sampleZero (pointDistance p q)) (Fraction.ofInt 1))
      (Fraction.ofInt 1) :=
    Fraction.equiv_trans (Fraction.add_equiv hz (Fraction.equiv_refl _)) (by decide)
  have hl : Fraction.le (pointDistance (sampleDownTwo p) (sampleDownTwo q))
      (Fraction.ofInt 1) := by
    unfold sampleDownTwo pointDistance pointNorm pointSub pointNeg
      pointAdd Fraction.le Fraction.add Fraction.abs Fraction.ofInt sampleZero
    decide
  exact Fraction.le_equiv_right hl (Fraction.equiv_symm hr)

/-- Empty schedules agree for every map and step size. -/
theorem zero_block_control (a : Point → Point) (h : Fraction)
    (s : Point × Point) :
    Fraction.equiv (stateDistance (fineAt a h s 0) (coarseAt a h s 0))
      sampleZero := stateDistance_self_zero s

/-- With zero cell duration, the first full/two-half block agrees exactly. -/
theorem zero_duration_block_control :
    Fraction.equiv
      (stateDistance (fineAt sampleDown sampleZero sampleState 1)
        (coarseAt sampleDown sampleZero sampleState 1)) sampleZero := by
  decide

/-- A constant downward map has `L=E=0` but its first refined block still
has a quarter-unit position defect at `h=1/2`. This catches accidental
omission of the `h²B` local term. -/
theorem constant_block_control :
    Fraction.equiv
      (stateDistance (fineAt sampleDown sampleHalf sampleState 1)
        (coarseAt sampleDown sampleHalf sampleState 1)) sampleQuarter := by
  decide

theorem constant_block_budget_control :
    Fraction.equiv
      (errorBudget sampleDown sampleHalf sampleZero sampleZero
        (Fraction.ofInt 1) sampleState 1) sampleQuarter := by
  decide

/-- Fine map `(0,-1)` versus coarse map `(0,-2)`, both from zero state:
the first block has one unit of velocity discrepancy plus a quarter-unit
position defect. A cross-map estimate cannot erase its `E` source. -/
theorem cross_constant_block_control :
    Fraction.equiv
      (stateDistance (fineAt sampleDown sampleHalf sampleState 1)
        (coarseAt sampleDownTwo sampleHalf sampleState 1))
      sampleFiveQuarters := by
  decide

theorem cross_constant_block_nonzero :
    ¬ Fraction.le
      (stateDistance (fineAt sampleDown sampleHalf sampleState 1)
        (coarseAt sampleDownTwo sampleHalf sampleState 1)) sampleZero := by
  unfold Fraction.le
  decide

/-- If the cross-map `E` source were silently erased, the derived local
coarse defect alone would give `1/2`, below the actual `5/4` error. -/
theorem cross_constant_requires_sample_error :
    ¬ Fraction.le
      (stateDistance (fineAt sampleDown sampleHalf sampleState 1)
        (coarseAt sampleDownTwo sampleHalf sampleState 1))
      (errorBudget sampleDownTwo sampleHalf sampleZero sampleZero
        (Fraction.ofInt 2) sampleState 1) := by
  unfold Fraction.le
  decide

end NewtonLimitDynamics.Polygon.FiniteAccumulation
