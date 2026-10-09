import Init

/-! Incommensurability of the diagonal: Aristotle, Prior Analytics I.23,
41a26-27. Original Greek, line-numbered transcript, PDF page 16:
https://schmidhauser.us/courses/06-analytica/notes/an.greek.pdf
ἀσύμμετρος ἡ διάμετρος διὰ τὸ γίνεσθαι τὰ περιττὰ ἴσα
τοῖς ἀρτίοις συμμέτρου τεθείσης.

Aristotle attests the parity contradiction under the supposition that the
diagonal is commensurable; he does not give the complete arithmetic proof
below. Status: editorial_interpretation, confidence high for that attestation,
not for an attribution of these exact descent steps to Aristotle. The original
English statements and proofs below give the precise project reconstruction.
No claim about the author of a lost proof, or about Euclid X.117, is made.

Mathlib comparison, source inspected at commit
9e6b3aac99b624d10c84653ab9c5357283b9b3b8:
https://github.com/leanprover-community/mathlib4/blob/9e6b3aac99b624d10c84653ab9c5357283b9b3b8/Mathlib/NumberTheory/Real/Irrational.lean
irrational_sqrt_two uses Nat.Prime.irrational_sqrt, which uses
irrational_sqrt_natCast_iff and primality's not_isSquare consequence. The
inspected route passes through Rat.isSquare_natCast_iff (Data/Rat/Lemmas.lean)
and real square-root identities (Analysis/Real/Sqrt.lean). The latter defines
NNReal.sqrt as the inverse of powOrderIso, and Real.sqrt via Real.toNNReal;
Irrational uses the rational image in the real numbers. These are modern
representations and general interfaces; the classical substitute needs only
parity and finite descent.
Basic/Real/Basic.lean defines Real using CauSeq.Completion.Cauchy. The inspected
source locators (all at the same pinned mathlib commit) are:
https://github.com/leanprover-community/mathlib4/blob/9e6b3aac99b624d10c84653ab9c5357283b9b3b8/Mathlib/Data/Rat/Lemmas.lean
https://github.com/leanprover-community/mathlib4/blob/9e6b3aac99b624d10c84653ab9c5357283b9b3b8/Mathlib/Analysis/Real/Sqrt.lean
https://github.com/leanprover-community/mathlib4/blob/9e6b3aac99b624d10c84653ab9c5357283b9b3b8/Mathlib/Basic/Real/Basic.lean
The checked substitute excludes integer ratios whose square is two, including unreduced
ratios; it does not construct a real square root or Euclidean diagonal.
Only Lean core arithmetic and logic are used, with no BarrowLib or ModernLib. -/

namespace ClassicsLib.Aristotle

/-- An even square has an even side. The two possible residues modulo two
are the arithmetic encoding of even/odd; an odd square has odd residue. -/
theorem even_of_even_square (a : Nat) (h : 2 ∣ a*a) : 2 ∣ a := by
  apply Nat.dvd_of_mod_eq_zero
  have hs := Nat.mod_eq_zero_of_dvd h
  rw [Nat.mul_mod] at hs
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · exact ha
  · simp [ha] at hs

/-- Halving an even numerator swaps the two sides of the square relation.
This is distributivity and cancellation by two, not a limiting theorem. -/
theorem halve_square_equation (a b u : Nat) (ha : a = 2*u)
    (h : a*a = 2*(b*b)) : b*b = 2*(u*u) := by
  have he : 2*(2*(u*u)) = 2*(b*b) := by
    calc
      2*(2*(u*u)) = (2*u)*(2*u) := by ac_rfl
      _ = a*a := by rw [ha]
      _ = 2*(b*b) := h
  exact (Nat.mul_left_cancel (by decide : 0 < 2) he).symm

/-- No nonzero denominator can represent a ratio whose square is two.
Parity makes both terms even and gives a smaller positive denominator;
strong induction formalizes the impossibility of continuing that descent. -/
theorem no_natural_ratio_square_two (a b : Nat) (hb : b ≠ 0) :
    a*a ≠ 2*(b*b) := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    intro heq
    have ha : 2 ∣ a*a := heq ▸ Nat.dvd_mul_right 2 (b*b)
    obtain ⟨u, hu⟩ := even_of_even_square a ha
    have hred := halve_square_equation a b u hu heq
    have hbe : 2 ∣ b*b := hred ▸ Nat.dvd_mul_right 2 (u*u)
    obtain ⟨v, hv⟩ := even_of_even_square b hbe
    have hnext := halve_square_equation b u v hv hred
    exact ih v (by omega) u (by omega) hnext

/-- Integer numerators and either sign of nonzero denominator are covered
by taking their natural absolute magnitudes. No rational reduction is assumed. -/
theorem no_integer_ratio_square_two (a b : Int) (hb : b ≠ 0) :
    a*a ≠ 2*(b*b) := by
  intro heq
  have hnat : a.natAbs*a.natAbs = 2*(b.natAbs*b.natAbs) := by
    have := congrArg Int.natAbs heq
    simpa only [Int.natAbs_mul, show Int.natAbs 2 = 2 by rfl] using this
  exact no_natural_ratio_square_two a.natAbs b.natAbs
    (by simpa using hb) hnat

end ClassicsLib.Aristotle
