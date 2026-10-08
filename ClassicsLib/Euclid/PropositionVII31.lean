import Init

/-! Euclid, Elements VII.31, original Greek (Stamatis transcription):
https://physics.ntua.gr/mourmouras/euclid_desktop/book7/postulate31.html
Ἅπας σύνθετος ἀριθμὸς ὑπὸ πρώτου τινὸς ἀριθμοῦ μετρεῖται.

Every composite number has a prime divisor. The proof repeatedly takes a
proper divisor; an indefinitely decreasing sequence of positive integers is
impossible. The checked natural-number formulation also admits a prime input,
which divides itself. Strong induction encodes this finite descent.
Status: explicit_dependency of Elements IX.20; confidence high. No claim that
the natural-number encoding reproduces Euclid's synthetic notion of number.
The definition below spells out the elementary divisor criterion for prime.
Only Lean core arithmetic and logic are used; no BarrowLib or ModernLib. -/

namespace ClassicsLib.Euclid

def Prime (p : Nat) : Prop :=
  1 < p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem prime_divisor (n : Nat) (hn : 1 < n) :
    ∃ p, Prime p ∧ p ∣ n := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hp : Prime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · have proper : ∃ d, d ∣ n ∧ 1 < d ∧ d < n := by
        by_cases hex : ∃ d, d ∣ n ∧ 1 < d ∧ d < n
        · exact hex
        · apply False.elim
          apply hp
          refine ⟨hn, fun d hd => ?_⟩
          by_cases h1 : d = 1
          · exact Or.inl h1
          · by_cases he : d = n
            · exact Or.inr he
            · have hpos := Nat.pos_of_dvd_of_pos hd (by omega : 0 < n)
              have hle := Nat.le_of_dvd (by omega : 0 < n) hd
              exact False.elim (hex ⟨d, hd, by omega, by omega⟩)
      obtain ⟨d, hd, hd1, hdn⟩ := proper
      obtain ⟨p, hp, hpd⟩ := ih d hdn hd1
      exact ⟨p, hp, Nat.dvd_trans hpd hd⟩

end ClassicsLib.Euclid
