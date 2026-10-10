import BarrowLib.Common.Quadratic
import BarrowLib.Common.RationalExhaustion

/-! Elementary exhaustion along a succession of refinements. No terminal
value is constructed. `TerminalLower` states only the lower comparisons that
a supplied terminal difference must respect; it does not assert its value.
The contradiction works for arbitrary ordered magnitudes. Core Rat equality
below is a concrete instance. -/
namespace NewtonLimitDynamics.Exhaustion

def Eventually (P : Nat → Prop) : Prop := ∃ N, ∀ n, N ≤ n → P n

theorem eventually_and {P R : Nat → Prop}
    (hp : Eventually P) (hr : Eventually R) : Eventually (fun n => P n ∧ R n) := by
  obtain ⟨N, hN⟩ := hp
  obtain ⟨M, hM⟩ := hr
  exact ⟨N + M, fun n hn => ⟨hN n (by omega), hM n (by omega)⟩⟩

def VanishingDifference {Q : Type} (g : Magnitudes Q) (gap : Nat → Q) : Prop :=
  ∀ d, g.positive d → Eventually (fun n => g.lt (gap n) d)

def TerminalLower {Q : Type} (g : Magnitudes Q) (gap : Nat → Q) (D : Q) : Prop :=
  ∀ d, g.positive d → g.lt d D → Eventually (fun n => g.lt d (gap n))

/-- A supposed positive terminal difference supplies a smaller positive
comparison. At a common refinement that comparison is both smaller and
larger than the actual difference, which contradicts strict order. -/
theorem no_positive_terminal {Q : Type} (g : Magnitudes Q) (gap : Nat → Q) (D : Q)
    (hsmall : VanishingDifference g gap) (hterminal : TerminalLower g gap D) :
    ¬ g.positive D := by
  intro hD
  obtain ⟨d, hd, hdD⟩ := g.shrink D hD
  obtain ⟨N, hN⟩ := eventually_and (hsmall d hd) (hterminal d hd hdD)
  have h := hN N (Nat.le_refl _)
  exact g.lt_irrefl d (g.lt_of_lt_le h.2 (g.lt_implies_le h.1))

theorem rational_terminal_zero (gap : Nat → Rat) (D : Rat)
    (hD : 0 ≤ D) (hsmall : VanishingDifference Rational.magnitudes gap)
    (hterminal : TerminalLower Rational.magnitudes gap D) : D = 0 := by
  have hn := no_positive_terminal Rational.magnitudes gap D hsmall hterminal
  change ¬ 0 < D at hn
  grind

/-- `h` is the remaining time before the supplied endpoint `T`, so
`0 < h < T` describes an actual before-end sample. Positivity of `T` is
required by the witness theorem; an empty time window cannot prove equality. -/
def BeforeEnd {Q : Type} (g : Magnitudes Q) (T : Q) (P : Q → Prop) : Prop :=
  Near g (fun h => g.lt h T → P h)

theorem before_end_and {Q : Type} (g : Magnitudes Q) (T : Q) (P R : Q → Prop)
    (hp : BeforeEnd g T P) (hr : BeforeEnd g T R) :
    BeforeEnd g T (fun h => P h ∧ R h) := by
  obtain ⟨d, hd, h⟩ := near_and g _ _ hp hr
  exact ⟨d, hd, fun t ht htd htT => ⟨(h t ht htd).1 htT, (h t ht htd).2 htT⟩⟩

theorem before_end_has_witness {Q : Type} (g : Magnitudes Q) (T : Q) (P : Q → Prop)
    (hT : g.positive T) (hp : BeforeEnd g T P) :
    ∃ h, g.positive h ∧ g.lt h T ∧ P h := by
  obtain ⟨d, hd, h⟩ := hp
  obtain ⟨e, he, hed⟩ := g.refine d T hd hT
  obtain ⟨t, ht, hte⟩ := g.shrink e he
  have hb := hed t ht hte
  exact ⟨t, ht, hb.2, h t ht hb.1 hb.2⟩

theorem no_positive_terminal_before_end {Q : Type} (g : Magnitudes Q)
    (T : Q) (hT : g.positive T) (gap : Q → Q) (D : Q)
    (hsmall : ∀ d, g.positive d → BeforeEnd g T (fun h => g.lt (gap h) d))
    (hterminal : ∀ d, g.positive d → g.lt d D →
      BeforeEnd g T (fun h => g.lt d (gap h))) : ¬ g.positive D := by
  intro hD
  obtain ⟨d, hd, hdD⟩ := g.shrink D hD
  obtain ⟨_, _, _, hlo, hhi⟩ := before_end_has_witness g T _ hT
    (before_end_and g T _ _ (hsmall d hd) (hterminal d hd hdD))
  exact g.lt_irrefl d (g.lt_of_lt_le hhi (g.lt_implies_le hlo))

end NewtonLimitDynamics.Exhaustion
