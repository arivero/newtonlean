import BarrowLib.Common.RationalMagnitudes

/-!
Elementary finite growth estimates with a common positive denominator.
These rational arithmetic bounds supply no completion, limiting trajectory,
geometric area or historical analytic theorem.
-/

namespace NewtonLimitDynamics.FiniteGrowth

def weightSum : List Int → Int
  | [] => 0
  | a :: xs => a + weightSum xs

def factorProduct (D : Int) : List Int → Int
  | [] => 1
  | a :: xs => (D + a) * factorProduct D xs

def Nonnegative (xs : List Int) : Prop := ∀ a ∈ xs, 0 ≤ a

theorem weightSum_nonnegative (xs : List Int) (hx : Nonnegative xs) :
    0 ≤ weightSum xs := by
  induction xs with
  | nil => exact Int.le_refl 0
  | cons a xs ih =>
      exact Int.add_nonneg (hx a (by simp))
        (ih (fun b hb => hx b (by simp [hb])))

theorem factorProduct_nonnegative (D : Int) (hD : 0 ≤ D)
    (xs : List Int) (hx : Nonnegative xs) : 0 ≤ factorProduct D xs := by
  induction xs with
  | nil => simp [factorProduct]
  | cons a xs ih =>
      exact Int.mul_nonneg (Int.add_nonneg hD (hx a (by simp)))
        (ih (fun b hb => hx b (by simp [hb])))

theorem cofactor_step (D a S : Int) (ha : 0 ≤ a) (hS : 0 ≤ S) :
    (D + a) * (D - (a + S)) ≤ D * (D - S) := by
  have hp : 0 ≤ a * a + a * S :=
    Int.add_nonneg (Int.mul_nonneg ha ha) (Int.mul_nonneg ha hS)
  have he : (D + a) * (D - (a + S)) + (a * a + a * S) =
      D * (D - S) := by
    simp only [Int.mul_sub, Int.sub_mul, Int.add_mul, Int.mul_add]
    ac_nf <;> omega
  omega

/-- Finite product/cofactor estimate. It even holds when the cofactor is
negative; the useful uniform conclusion additionally bounds the total. -/
theorem cofactor_bound (D : Int) (hD : 0 < D)
    (xs : List Int) (hx : Nonnegative xs) :
    factorProduct D xs * (D - weightSum xs) ≤ D ^ (xs.length + 1) := by
  induction xs with
  | nil => simp [factorProduct, weightSum, Int.pow_succ]
  | cons a xs ih =>
      have ha := hx a (by simp)
      have ht : Nonnegative xs := fun b hb => hx b (by simp [hb])
      have hP := factorProduct_nonnegative D (Int.le_of_lt hD) xs ht
      have hs := weightSum_nonnegative xs ht
      have step := Int.mul_le_mul_of_nonneg_left (cofactor_step D a (weightSum xs) ha hs) hP
      have next := Int.mul_le_mul_of_nonneg_left (ih ht) (Int.le_of_lt hD)
      simp only [factorProduct, weightSum, List.length_cons]
      rw [Int.pow_succ']
      calc
        (D + a) * factorProduct D xs * (D - (a + weightSum xs)) =
            factorProduct D xs * ((D + a) * (D - (a + weightSum xs))) := by ac_rfl
        _ ≤ factorProduct D xs * (D * (D - weightSum xs)) := step
        _ = D * (factorProduct D xs * (D - weightSum xs)) := by ac_rfl
        _ ≤ D * D ^ (xs.length + 1) := next

/-- Uniform finite growth at small total increment, including empty lists. -/
theorem uniform_product_bound (D : Int) (hD : 0 < D)
    (xs : List Int) (hx : Nonnegative xs) (hsmall : 2 * weightSum xs ≤ D) :
    factorProduct D xs ≤ 2 * D ^ xs.length := by
  have hP := factorProduct_nonnegative D (Int.le_of_lt hD) xs hx
  have hco := cofactor_bound D hD xs hx
  have hs : D ≤ 2 * (D - weightSum xs) := by omega
  have hm := Int.mul_le_mul_of_nonneg_left hs hP
  have hb := Int.mul_le_mul_of_nonneg_left hco (by decide : (0 : Int) ≤ 2)
  have hchain : factorProduct D xs * D ≤ (2 * D ^ xs.length) * D := by
    calc
      factorProduct D xs * D ≤ factorProduct D xs * (2 * (D - weightSum xs)) := hm
      _ = 2 * (factorProduct D xs * (D - weightSum xs)) := by ac_rfl
      _ ≤ 2 * D ^ (xs.length + 1) := hb
      _ = (2 * D ^ xs.length) * D := by rw [Int.pow_succ, Int.mul_assoc]
  exact Int.le_of_mul_le_mul_right hchain hD

def factor (D : Int) (hD : 0 < D) (a : Int) : Fraction := ⟨D + a, D, hD⟩

def amplification (D : Int) (hD : 0 < D) (xs : List Int) : Fraction :=
  ⟨factorProduct D xs, D ^ xs.length, Int.pow_pos hD⟩

theorem factor_eq_one_add (D : Int) (hD : 0 < D) (a : Int) :
    Fraction.equiv (factor D hD a)
      (Fraction.add (Fraction.ofInt 1) ⟨a, D, hD⟩) := by
  simp only [factor, Fraction.equiv, Fraction.add, Fraction.ofInt,
    Int.one_mul, Int.mul_one]

theorem amplification_empty (D : Int) (hD : 0 < D) :
    Fraction.equiv (amplification D hD []) (Fraction.ofInt 1) := by
  simp [amplification, factorProduct, Fraction.equiv, Fraction.ofInt]

theorem amplification_cons (D : Int) (hD : 0 < D) (a : Int) (xs : List Int) :
    Fraction.equiv (amplification D hD (a :: xs))
      (Fraction.mul (factor D hD a) (amplification D hD xs)) := by
  simp only [amplification, factor, factorProduct, List.length_cons,
    Fraction.equiv, Fraction.mul, Int.pow_succ']

theorem amplification_nonnegative (D : Int) (hD : 0 < D)
    (xs : List Int) (hx : Nonnegative xs) :
    0 ≤ (amplification D hD xs).num :=
  factorProduct_nonnegative D (Int.le_of_lt hD) xs hx

theorem uniform_amplification (D : Int) (hD : 0 < D)
    (xs : List Int) (hx : Nonnegative xs) (hsmall : 2 * weightSum xs ≤ D) :
    Fraction.le (amplification D hD xs) (Fraction.ofInt 2) := by
  simpa only [amplification, Fraction.le, Fraction.ofInt, Int.mul_one] using
    uniform_product_bound D hD xs hx hsmall

theorem weightSum_append (xs ys : List Int) :
    weightSum (xs ++ ys) = weightSum xs + weightSum ys := by
  induction xs with
  | nil => simp [weightSum]
  | cons a xs ih => simp only [List.cons_append, weightSum, ih, Int.add_assoc]

theorem factorProduct_append (D : Int) (xs ys : List Int) :
    factorProduct D (xs ++ ys) = factorProduct D xs * factorProduct D ys := by
  induction xs with
  | nil => simp [factorProduct]
  | cons a xs ih => simp only [List.cons_append, factorProduct, ih, Int.mul_assoc]

theorem denominator_power_add (D : Int) (m n : Nat) :
    D ^ (m + n) = D ^ m * D ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [← Nat.add_assoc, Int.pow_succ, ih, Int.mul_assoc]

theorem amplification_append (D : Int) (hD : 0 < D) (xs ys : List Int) :
    Fraction.equiv (amplification D hD (xs ++ ys))
      (Fraction.mul (amplification D hD xs) (amplification D hD ys)) := by
  simp only [amplification, factorProduct_append, List.length_append,
    denominator_power_add, Fraction.equiv, Fraction.mul]

theorem weightSum_replicate (a : Int) (n : Nat) :
    weightSum (List.replicate n a) = (n : Int) * a := by
  induction n with
  | zero => simp [weightSum]
  | succ n ih =>
      simp only [List.replicate_succ, weightSum, ih, Int.natCast_add,
        Int.natCast_one, Int.add_mul, Int.one_mul]
      omega

theorem factorProduct_replicate (D a : Int) (n : Nat) :
    factorProduct D (List.replicate n a) = (D + a) ^ n := by
  induction n with
  | zero => simp [factorProduct]
  | succ n ih => simp only [List.replicate_succ, factorProduct, ih, Int.pow_succ']

theorem zero_increments (D : Int) (hD : 0 < D) (n : Nat) :
    Fraction.equiv (amplification D hD (List.replicate n 0)) (Fraction.ofInt 1) := by
  simp only [amplification, factorProduct_replicate, List.length_replicate,
    Fraction.equiv, Fraction.ofInt, Int.add_zero, Int.mul_one, Int.one_mul]

theorem boundary_sample :
    Fraction.equiv (amplification 4 (by decide) [1, 1]) ⟨25, 16, by decide⟩ := by
  unfold Fraction.equiv
  decide

theorem missing_smallness_counterexample :
    ¬ Fraction.le (amplification 1 (by decide) [1, 1]) (Fraction.ofInt 2) := by
  unfold Fraction.le amplification factorProduct
  decide

end NewtonLimitDynamics.FiniteGrowth
