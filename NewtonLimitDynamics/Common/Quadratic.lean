/- No mathlib. Magnitudes and ratios are abstract: this file supplies logical
   bookkeeping for shrinking intervals and ordered enclosures, not calculus. -/
namespace NewtonLimitDynamics

structure Magnitudes (Q : Type) where
  positive : Q → Prop
  lt : Q → Q → Prop
  le : Q → Q → Prop
  /-- Inhabitance and comparison brackets prevent vacuous limits. -/
  inhabited_positive : ∃ d, positive d
  lt_irrefl : ∀ a, ¬ lt a a
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  lt_implies_le : ∀ {a b}, lt a b → le a b
  surrounds : ∀ c, ∃ a b, lt a c ∧ lt c b
  lt_of_lt_le : ∀ {a b c}, lt a b → le b c → lt a c
  lt_of_le_lt : ∀ {a b c}, le a b → lt b c → lt a c
  /-- No smallest positive interval: neighborhoods must not be vacuous. -/
  shrink : ∀ d, positive d → ∃ h, positive h ∧ lt h d
  /-- Two permitted interval bounds admit a common smaller positive bound. -/
  refine : ∀ a b, positive a → positive b →
    ∃ d, positive d ∧ ∀ h, positive h → lt h d → lt h a ∧ lt h b

variable {Q : Type}

def Near (g : Magnitudes Q) (P : Q → Prop) : Prop :=
  ∃ d, g.positive d ∧ ∀ h, g.positive h → g.lt h d → P h

theorem near_and (g : Magnitudes Q) (P R : Q → Prop)
    (hp : Near g P) (hr : Near g R) : Near g (fun h => P h ∧ R h) := by
  obtain ⟨a, ha, hpa⟩ := hp
  obtain ⟨b, hb, hrb⟩ := hr
  obtain ⟨d, hd, hdab⟩ := g.refine a b ha hb
  refine ⟨d, hd, ?_⟩
  intro h hh hhd
  obtain ⟨hha, hhb⟩ := hdab h hh hhd
  exact ⟨hpa h hh hha, hrb h hh hhb⟩

/-- Ultimate equality expressed by eventual enclosure between arbitrary
    surrounding ratios. This is an encoding, not a quoted Newton definition. -/
def Ultimate (g : Magnitudes Q) (ratio : Q → Q) (c : Q) : Prop :=
  ∀ a b, g.lt a c → g.lt c b →
    Near g (fun h => g.lt a (ratio h) ∧ g.lt (ratio h) b)

/-- Logical squeeze justified by order and unlimited common refinement.
    Lower and upper geometric limits must be supplied, not assumed proved. -/
theorem enclosure_reconstruction (g : Magnitudes Q)
    (ratio lower upper : Q → Q) (c : Q)
    (hl : Ultimate g lower c) (hu : Ultimate g upper c)
    (hb : Near g (fun h => g.le (lower h) (ratio h) ∧
      g.le (ratio h) (upper h))) : Ultimate g ratio c := by
  intro a b hac hcb
  obtain ⟨d, hd, hx⟩ := near_and g _ _ (near_and g _ _
    (hl a b hac hcb) (hu a b hac hcb)) hb
  refine ⟨d, hd, ?_⟩
  intro h hh hhd
  obtain ⟨⟨⟨hal, _⟩, ⟨_, hub⟩⟩, ⟨hlr, hru⟩⟩ := hx h hh hhd
  exact ⟨g.lt_of_lt_le hal hlr, g.lt_of_le_lt hru hub⟩

/-- Every eventual assertion has an actual positive witness. -/
theorem near_has_witness (g : Magnitudes Q) (P : Q → Prop)
    (h : Near g P) : ∃ x, g.positive x ∧ P x := by
  obtain ⟨d, hd, hp⟩ := h
  obtain ⟨x, hx, hxd⟩ := g.shrink d hd
  exact ⟨x, hx, hp x hx hxd⟩

theorem not_near_false (g : Magnitudes Q) : ¬ Near g (fun _ => False) := by
  intro h
  obtain ⟨_, _, hf⟩ := near_has_witness g _ h
  exact hf

end NewtonLimitDynamics
