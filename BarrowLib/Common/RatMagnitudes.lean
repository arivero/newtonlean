import BarrowLib.Common.Quadratic

/- Core Rat realizes the existing ordered-magnitude interface. This is
   encoding infrastructure, not a new historically attributed result.
   It is separate from the temporary legacy Fraction model. -/
namespace NewtonLimitDynamics.Rational
/-- The concrete core-Rat model of ordered magnitudes. -/
def magnitudes : Magnitudes Rat where
  positive := fun a => 0 < a
  lt := (· < ·)
  le := (· ≤ ·)
  inhabited_positive := ⟨1, by decide +kernel⟩
  lt_irrefl := fun _ => Rat.lt_irrefl
  le_refl := fun _ => Rat.le_refl
  le_trans := Rat.le_trans
  lt_implies_le := Rat.le_of_lt
  surrounds := by intro c; exact ⟨c-1,c+1,by grind⟩
  lt_of_lt_le := by intros; grind
  lt_of_le_lt := by intros; grind
  shrink := by intro d hd; exact ⟨d/2,by grind⟩
  refine := by
    intro a b ha hb
    by_cases h : a ≤ b
    · exact ⟨a, ha, by grind⟩
    · exact ⟨b, hb, by grind⟩

end NewtonLimitDynamics.Rational
