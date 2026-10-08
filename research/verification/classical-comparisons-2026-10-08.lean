import ClassicsLib
import Lean

/-! Scope controls for the two classical comparison examples. Finite-list
Euclid includes an empty list, repetitions and a composite product-plus-one.
The parity proof covers unreduced ratios and both integer signs, and explicitly
requires a nonzero denominator. Compiled traversal requires the displayed
classical helpers and excludes BarrowLib, ModernLib, Newton and mathlib.
These controls share the Lean kernel and core arithmetic with the proofs. -/

open ClassicsLib.Euclid ClassicsLib.Aristotle

private theorem prime_two : Prime 2 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have := Nat.pos_of_dvd_of_pos hd (by decide : 0 < 2)
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

example : ∃ p, Prime p ∧ p ∉ ([] : List Nat) := infinitude_primes [] (by simp)
example : ∃ p, Prime p ∧ p ∉ [2,2] :=
  infinitude_primes [2,2] (by
    intro p hp
    have he : p=2 := by simpa using hp
    rw [he]
    exact prime_two)
example : finiteProduct [3,5,7]+1 = 106 := by decide
example : 2 ∣ finiteProduct [3,5,7]+1 ∧ 2 ∉ [3,5,7] := by decide
example : ∃ p, Prime p ∧ p ∉ [3,5,7] :=
  prime_outside_positive_list [3,5,7] (by intro p hp; simp at hp; omega)
example : ¬ Prime 1 := by intro h; have := h.1; omega
example : ¬ Prime 4 := by
  intro h
  have := h.2 2 (by decide)
  omega
example : ∃ p, 100 ≤ p ∧ Prime p := exists_prime_ge 100

example : 2 ∣ 12 := even_of_even_square 12 (by decide)
example : (3 : Nat)*(3 : Nat) ≠ 2*(2*2) := no_natural_ratio_square_two 3 2 (by decide)
example : (6 : Nat)*(6 : Nat) ≠ 2*(4*4) := no_natural_ratio_square_two 6 4 (by decide)
example : (-6 : Int)*(-6) ≠ 2*((-4)*(-4)) := no_integer_ratio_square_two (-6) (-4) (by decide)
example : (0 : Nat)*0 = 2*(0*0) := by decide

#print axioms infinitude_primes
#print axioms exists_prime_ge
#print axioms no_integer_ratio_square_two

open Lean in
run_elab do
  let env ← getEnv
  for (root, required) in #[
      (`ClassicsLib.Euclid.infinitude_primes,
        #[`ClassicsLib.Euclid.prime_divisor, `ClassicsLib.Euclid.divides_finiteProduct]),
      (`ClassicsLib.Euclid.exists_prime_ge,
        #[`ClassicsLib.Euclid.prime_outside_positive_list]),
      (`ClassicsLib.Aristotle.no_integer_ratio_square_two,
        #[`ClassicsLib.Aristotle.even_of_even_square,
          `ClassicsLib.Aristotle.halve_square_equation])] do
    let mut todo := #[root]
    let mut used : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      unless used.contains name do
        used := used.insert name
        if let some info := env.find? name then
          todo := todo ++ info.type.getUsedConstants ++
            ((info.value? true).map Expr.getUsedConstants |>.getD #[])
    for needed in required do
      unless used.contains needed do throwError "{root} omits {needed}"
    for dependency in used do
      if let some idx := env.getModuleIdxFor? dependency then
        let module := env.header.moduleNames[idx]!.toString
        if #["BarrowLib", "ModernLib", "NewtonLimitDynamics", "Mathlib"].any module.startsWith then
          throwError "{root} uses forbidden dependency {dependency} from {module}"
  logInfo "Classical comparisons use their arithmetic helpers and no later project library."
