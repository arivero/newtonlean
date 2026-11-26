import Std

/-! A rational-time obstruction for the slope chart used in Proposition I.
The cleared equation below is h(a/b) = 1/7 for
h(t) = t + 2t³/3 + t⁵/5. Its original derivation and geometric scope
are in research/PROP_I_PATH_DEFECT.md. This is a diagnostic, outside
the historical proof dependencies. -/
namespace RationalTimeSlope

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem residues : ∀ a b : Fin 49,
    (21 * a.val^5 + 70 * a.val^3 * b.val^2 + 105 * a.val * b.val^4) % 49 =
      (15 * b.val^5) % 49 → a.val % 7 = 0 ∧ b.val % 7 = 0 := by decide

private def Eq49 (a b : Nat) := a % 49 = b % 49

private theorem eqMul {a b c d : Nat} (h : Eq49 a b) (k : Eq49 c d) :
    Eq49 (a*c) (b*d) := by
  change a % 49 = b % 49 at h
  change c % 49 = d % 49 at k
  change _ % 49 = _ % 49
  rw [Nat.mul_mod a c 49, Nat.mul_mod b d 49, h, k]

private theorem eqAdd {a b c d : Nat} (h : Eq49 a b) (k : Eq49 c d) :
    Eq49 (a+c) (b+d) := by
  change a % 49 = b % 49 at h
  change c % 49 = d % 49 at k
  change _ % 49 = _ % 49
  rw [Nat.add_mod a c 49, Nat.add_mod b d 49, h, k]

private theorem eqPow {a b : Nat} (h : Eq49 a b) (n : Nat) :
    Eq49 (a^n) (b^n) := by
  change a % 49 = b % 49 at h
  change _ % 49 = _ % 49
  rw [Nat.pow_mod a n 49, Nat.pow_mod b n 49, h]

/-- Every natural solution of the cleared equation has a common factor seven. -/
theorem common_seven (a b : Nat)
    (h : 21*a^5 + 70*a^3*b^2 + 105*a*b^4 = 15*b^5) :
    a % 7 = 0 ∧ b % 7 = 0 := by
  let x : Fin 49 := ⟨a % 49, Nat.mod_lt _ (by decide)⟩
  let y : Fin 49 := ⟨b % 49, Nat.mod_lt _ (by decide)⟩
  have hx : Eq49 x.val a := by simp [Eq49, x]
  have hy : Eq49 y.val b := by simp [Eq49, y]
  have lhs := eqAdd (eqAdd (eqMul (rfl : Eq49 21 21) (eqPow hx 5))
    (eqMul (eqMul (rfl : Eq49 70 70) (eqPow hx 3)) (eqPow hy 2)))
    (eqMul (eqMul (rfl : Eq49 105 105) hx) (eqPow hy 4))
  have rhs := eqMul (rfl : Eq49 15 15) (eqPow hy 5)
  unfold Eq49 at lhs rhs
  have cert := residues x y (lhs.trans ((congrArg (fun z : Nat => z % 49) h).trans rhs.symm))
  have div : 7 ∣ 49 := by decide
  simpa only [x, y, Nat.mod_mod_of_dvd _ div] using cert

end RationalTimeSlope
