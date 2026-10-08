import ClassicsLib.Euclid.PropositionVII31

/-! Euclid, Elements IX.20, original Greek (Stamatis transcription):
https://physics.ntua.gr/mourmouras/euclid/book9/postulate20.html
Οἱ πρῶτοι ἀριθμοὶ πλείους εἰσὶ παντὸς τοῦ προτεθέντος
πλήθους πρώτων ἀριθμῶν.

There are more primes than any proposed finite collection. Euclid takes a
least common multiple, adds one, and uses VII.31 if the result is composite.
A previously listed prime would then measure the unit, which is impossible.
Here an explicitly multiplied finite list supplies a common multiple; its
minimality is unused. This substitution is editorial_interpretation, confidence
high, rather than a quotation of Euclid's chosen construction. The finite
product helpers below have their own English statements and checked proofs.

Mathlib comparison, source inspected at commit
9e6b3aac99b624d10c84653ab9c5357283b9b3b8:
https://github.com/leanprover-community/mathlib4/blob/9e6b3aac99b624d10c84653ab9c5357283b9b3b8/Mathlib/Data/Nat/Prime/Infinite.lean
Nat.exists_infinite_primes chooses minFac (n!+1), proves it prime, and rules
out p <= n using dvd_factorial and a divisor of one. This mathematical route
needs no post-Principia theorem: factorial packages a finite common multiple,
and minFac packages VII.31's prime-divisor step. The separate BddAbove wrapper
uses modern set/order notation. Neither mathlib nor that wrapper is imported.
The checked substitutes below expose the finite-list argument and the stronger
numeric bound separately. Known mathematics remains attributed to Euclid. -/

namespace ClassicsLib.Euclid

def finiteProduct : List Nat → Nat
  | [] => 1
  | p :: ps => p * finiteProduct ps

theorem finiteProduct_positive (ps : List Nat)
    (hpos : ∀ p, p ∈ ps → 0 < p) : 0 < finiteProduct ps := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    exact Nat.mul_pos (hpos p (by simp))
      (ih (fun q hq => hpos q (by simp [hq])))

theorem divides_finiteProduct (ps : List Nat) (p : Nat) (hp : p ∈ ps) :
    p ∣ finiteProduct ps := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with he | ht
    · subst q
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih ht) q

/-- The common-multiple argument works for any finite list of positive
integers, whether or not every entry is prime. -/
theorem prime_outside_positive_list (ps : List Nat)
    (hpos : ∀ p, p ∈ ps → 0 < p) : ∃ p, Prime p ∧ p ∉ ps := by
  obtain ⟨p, hp, hd⟩ := prime_divisor (finiteProduct ps + 1)
    (by have := finiteProduct_positive ps hpos; omega)
  refine ⟨p, hp, fun hmem => ?_⟩
  have hone : p ∣ 1 := (Nat.dvd_add_iff_right (divides_finiteProduct ps p hmem)).mpr hd
  have := Nat.eq_one_of_dvd_one hone
  have := hp.1
  omega

/-- Elements IX.20 in its finite-collection form. Repetitions and an empty
collection are allowed; the new prime is distinct from every entry. -/
theorem infinitude_primes (ps : List Nat)
    (hprime : ∀ p, p ∈ ps → Prime p) : ∃ p, Prime p ∧ p ∉ ps :=
  prime_outside_positive_list ps (fun p hp => by have := (hprime p hp).1; omega)

/-- Numeric reformulation for comparison with Nat.exists_infinite_primes.
The finite collection 1,...,n suffices; no infinite set object is needed. -/
theorem exists_prime_ge (n : Nat) : ∃ p, n ≤ p ∧ Prime p := by
  let ps := (List.range n).map (fun i => i + 1)
  obtain ⟨p, hp, hnot⟩ := prime_outside_positive_list ps (by
    intro q hq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    omega)
  refine ⟨p, ?_, hp⟩
  by_cases h : n ≤ p
  · exact h
  · have hmem : p ∈ ps := by
      apply List.mem_map.mpr
      refine ⟨p-1, List.mem_range.mpr (by omega), ?_⟩
      have := hp.1
      omega
    exact False.elim (hnot hmem)

end ClassicsLib.Euclid
