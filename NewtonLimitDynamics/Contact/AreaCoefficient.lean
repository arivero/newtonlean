import NewtonLimitDynamics.Contact.FiniteSums

namespace NewtonLimitDynamics.Contact

private theorem zero_of_scaled_bounds (delta C : Int)
    (h : ∀ n : Nat, 0 < n → (n : Int)*delta ≤ C ∧ (n : Int)*(-delta) ≤ C) : delta = 0 := by
  let n := C.natAbs + 1
  have hn : 0 < n := by omega
  obtain ⟨hu, hl⟩ := h n hn
  have habs : C ≤ (C.natAbs : Int) := Int.le_natAbs
  have hnlarge : C < (n : Int) := by dsimp [n]; omega
  have hnp : 0 ≤ (n : Int) := by omega
  by_cases hp : 0 < delta
  · have hd : 1 ≤ delta := by omega
    have hm := Int.mul_le_mul_of_nonneg_left hd hnp
    simp only [Int.mul_one] at hm
    omega
  · by_cases hm : delta < 0
    · have hd : 1 ≤ -delta := by omega
      have hb := Int.mul_le_mul_of_nonneg_left hd hnp
      simp only [Int.mul_one] at hb
      omega
    · omega

def lowerParabola (n : Nat) (hn : 0 < n) : Fraction :=
  ⟨(nsum (fun i => i*i) n : Int), (n*n*n : Nat),
    Int.ofNat_lt.mpr (Nat.mul_pos (Nat.mul_pos hn hn) hn)⟩
def upperParabola (n : Nat) (hn : 0 < n) : Fraction :=
  ⟨(nsum (fun i => i*i) n + n*n : Nat), (n*n*n : Nat),
    Int.ofNat_lt.mpr (Nat.mul_pos (Nat.mul_pos hn hn) hn)⟩

/-- Rectangle enclosure determines the normalized parabolic area as 1/3.
    Only finite sums and rational order are used. The geometric assertion that
    a selected curve's area obeys these rectangle enclosures is the premise. -/
theorem parabolic_area_coefficient (area : Fraction)
    (enclosed : ∀ n : Nat, (hn : 0 < n) →
      Fraction.le (lowerParabola n hn) area ∧ Fraction.le area (upperParabola n hn)) :
    Fraction.equiv area ⟨1, 3, by decide⟩ := by
  have heq : 3*area.num-area.den = 0 := by
    apply zero_of_scaled_bounds _ (2*area.den)
    intro n hn
    let N : Int := n
    let S : Int := nsum (fun i => i*i) n
    have hN : 0 < N := Int.ofNat_lt.mpr hn
    have hNN := Int.mul_pos hN hN
    obtain ⟨hl, hu⟩ := enclosed n hn
    change S*area.den ≤ area.num*(N*N*N) at hl
    change area.num*(N*N*N) ≤ (S+N*N)*area.den at hu
    have hi := congrArg (fun x : Nat => (x : Int)) (quadratic_rectangles n)
    simp only [Int.ofNat_add, Int.ofNat_mul] at hi
    have hid := congrArg (fun x : Int => x*area.den) hi
    have ident : 6*(S*area.den)+3*(N*N*area.den) =
        2*(N*N*N*area.den)+N*area.den := by
      simpa only [Int.add_mul, Int.mul_assoc] using hid
    have hlo := Int.mul_le_mul_of_nonneg_left hl (by decide : (0 : Int) ≤ 6)
    have hhi := Int.mul_le_mul_of_nonneg_left hu (by decide : (0 : Int) ≤ 6)
    simp only [Int.add_mul, Int.mul_add] at hhi
    have wpos := Int.mul_pos hN area.den_pos
    have wle : N*area.den ≤ N*N*area.den := by
      have hge : (1 : Int) ≤ N := by omega
      have ht := Int.mul_le_mul_of_nonneg_right hge (Int.le_of_lt wpos)
      simpa only [Int.one_mul, Int.mul_assoc] using ht
    have hupper : 6*(area.num*(N*N*N))-2*(N*N*N*area.den) ≤ 4*(N*N*area.den) := by omega
    have hlower : 2*(N*N*N*area.den)-6*(area.num*(N*N*N)) ≤ 4*(N*N*area.den) := by omega
    have factor : 2*(N*(3*area.num-area.den))*(N*N) =
        6*(area.num*(N*N*N))-2*(N*N*N*area.den) := by
      simp only [Int.mul_sub, Int.sub_mul]
      have six : (6 : Int) = 2*3 := by decide
      rw [six]
      congr 1 <;> ac_rfl
    have factor' : 2*(N*(area.den-3*area.num))*(N*N) =
        2*(N*N*N*area.den)-6*(area.num*(N*N*N)) := by
      simp only [Int.mul_sub, Int.sub_mul]
      have six : (6 : Int) = 2*3 := by decide
      rw [six]
      congr 1 <;> ac_rfl
    have rhs : 4*(N*N*area.den) = (4*area.den)*(N*N) := by ac_rfl
    rw [← factor, rhs] at hupper
    rw [← factor', rhs] at hlower
    have hu' := Int.le_of_mul_le_mul_right hupper hNN
    have hl' := Int.le_of_mul_le_mul_right hlower hNN
    have hnneg : N*(-(3*area.num-area.den)) = N*(area.den-3*area.num) := by
      congr 1
      omega
    change N*(3*area.num-area.den) ≤ 2*area.den ∧ N*(-(3*area.num-area.den)) ≤ 2*area.den
    rw [hnneg]
    omega
  unfold Fraction.equiv
  dsimp
  omega

def lowerLinear (n : Nat) (hn : 0 < n) : Fraction :=
  ⟨(nsum (fun i => i) n : Int), (n*n : Nat),
    Int.ofNat_lt.mpr (Nat.mul_pos hn hn)⟩
def upperLinear (n : Nat) (hn : 0 < n) : Fraction :=
  ⟨(nsum (fun i => i) n + n : Nat), (n*n : Nat),
    Int.ofNat_lt.mpr (Nat.mul_pos hn hn)⟩

/-- Normalized linear velocity area is 1/2, from finite rectangles alone. -/
theorem linear_area_coefficient (area : Fraction)
    (enclosed : ∀ n : Nat, (hn : 0 < n) →
      Fraction.le (lowerLinear n hn) area ∧ Fraction.le area (upperLinear n hn)) :
    Fraction.equiv area ⟨1, 2, by decide⟩ := by
  have heq : 2*area.num-area.den = 0 := by
    apply zero_of_scaled_bounds _ area.den
    intro n hn
    let N : Int := n
    let S : Int := nsum (fun i => i) n
    have hN : 0 < N := Int.ofNat_lt.mpr hn
    obtain ⟨hl, hu⟩ := enclosed n hn
    change S*area.den ≤ area.num*(N*N) at hl
    change area.num*(N*N) ≤ (S+N)*area.den at hu
    have hi := congrArg (fun x : Nat => (x : Int)) (linear_rectangles n)
    simp only [Int.ofNat_add, Int.ofNat_mul] at hi
    have hid := congrArg (fun x : Int => x*area.den) hi
    have ident : 2*(S*area.den)+N*area.den = N*N*area.den := by
      simpa only [Int.add_mul, Int.mul_assoc] using hid
    have hlo := Int.mul_le_mul_of_nonneg_left hl (by decide : (0 : Int) ≤ 2)
    have hhi := Int.mul_le_mul_of_nonneg_left hu (by decide : (0 : Int) ≤ 2)
    simp only [Int.add_mul, Int.mul_add] at hhi
    have hupper : 2*(area.num*(N*N))-N*N*area.den ≤ N*area.den := by omega
    have hlower : N*N*area.den-2*(area.num*(N*N)) ≤ N*area.den := by omega
    have factor : (N*(2*area.num-area.den))*N = 2*(area.num*(N*N))-N*N*area.den := by
      simp only [Int.mul_sub, Int.sub_mul]
      congr 1 <;> ac_rfl
    have factor' : (N*(area.den-2*area.num))*N = N*N*area.den-2*(area.num*(N*N)) := by
      simp only [Int.mul_sub, Int.sub_mul]
      congr 1 <;> ac_rfl
    have rhs : N*area.den = area.den*N := by ac_rfl
    rw [← factor, rhs] at hupper
    rw [← factor', rhs] at hlower
    have hu' := Int.le_of_mul_le_mul_right hupper hN
    have hl' := Int.le_of_mul_le_mul_right hlower hN
    have hnneg : N*(-(2*area.num-area.den)) = N*(area.den-2*area.num) := by
      congr 1
      omega
    change N*(2*area.num-area.den) ≤ area.den ∧ N*(-(2*area.num-area.den)) ≤ area.den
    rw [hnneg]
    exact ⟨hu', hl'⟩
  unfold Fraction.equiv
  dsimp
  omega

/-- Constant-force example with unit tangential speed and zero initial normal
    velocity. Similarity scales normalized rectangle areas. Mechanical
    identification with displacement/defect is still separate from this
    geometric coefficient theorem. -/
theorem constant_force_area_coefficients (acc time linearArea parabolaArea : Fraction)
    (hlinear : ∀ n : Nat, (hn : 0 < n) →
      Fraction.le (lowerLinear n hn) linearArea ∧ Fraction.le linearArea (upperLinear n hn))
    (hparabola : ∀ n : Nat, (hn : 0 < n) →
      Fraction.le (lowerParabola n hn) parabolaArea ∧ Fraction.le parabolaArea (upperParabola n hn)) :
    Fraction.equiv (Fraction.mul (Fraction.mul acc (Fraction.mul time time)) linearArea)
      (Fraction.half (Fraction.mul acc (Fraction.mul time time))) ∧
    Fraction.equiv (Fraction.mul (Fraction.half (Fraction.mul acc (Fraction.mul time (Fraction.mul time time)))) parabolaArea)
      (Fraction.mul ⟨1, 6, by decide⟩ (Fraction.mul acc (Fraction.mul time (Fraction.mul time time)))) := by
  constructor
  · apply Fraction.equiv_trans (Fraction.mul_equiv_left _ (linear_area_coefficient linearArea hlinear))
    unfold Fraction.equiv Fraction.mul Fraction.half
    dsimp
    simp only [Int.one_mul, Int.mul_one]
    ac_rfl
  · apply Fraction.equiv_trans (Fraction.mul_equiv_left _ (parabolic_area_coefficient parabolaArea hparabola))
    unfold Fraction.equiv Fraction.mul Fraction.half
    dsimp
    simp only [Int.one_mul, Int.mul_one]
    have six : (6 : Int) = 2*3 := by decide
    rw [six]
    ac_rfl

end NewtonLimitDynamics.Contact
