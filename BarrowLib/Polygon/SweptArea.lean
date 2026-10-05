import BarrowLib.Polygon.FanValues
import BarrowLib.Polygon.DyadicNodes

/-! Area swept by a curve, defined intrinsically by triangle fans at its
actual dyadic time nodes. Unsigned fans count repeated coverage with
multiplicity; oriented fans keep the signed winding convention. Neither is
the unsigned union content between two paths. No area existence is assumed. -/

namespace NewtonLimitDynamics.Polygon.SweptArea
open NewtonLimitDynamics
open TimeSubdivision HarmonicDyadic HarmonicBinaryPrefix HarmonicTimeRealization BinaryTime
open CauchyValues PositionValues DyadicNodes

def AreaAt (unsigned : Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue) (t : BinaryTime T hT) (area : Value) : Prop :=
  ∀ b : Nat → Bool, (Quotient.mk _ b : BinaryTime T hT)=t →
    ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m, N≤m →
      Within (FanValues.halfValue (FanValues.fanValue unsigned
        (fun k => (curve (nodeTime T hT m k)).val) (ticks b m))) area eps

/-- The actual curve-fan limit determines at most one swept area. Existence
is a separate construction, never a field of this definition. -/
theorem area_unique (unsigned : Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (curve : BinaryTime T hT → PositionValue) (t : BinaryTime T hT) (a b : Value)
    (ha : AreaAt unsigned T hT curve t a) (hb : AreaAt unsigned T hT curve t b) : a=b := by
  have hsmall : ∀ eps : Fraction, 0 < eps.num → Within a b eps := by
    intro eps heps
    induction t using Quotient.inductionOn with
    | _ c =>
      obtain ⟨N,hN⟩ := ha c rfl eps.half heps
      obtain ⟨M,hM⟩ := hb c rfl eps.half heps
      exact within_mono _ _ _ _ (Fraction.le_of_equiv (Fraction.half_add_self eps))
        (within_triangle _ _ _ _ _ (within_symm _ _ _ (hN (max N M) (Nat.le_max_left _ _)))
          (hM (max N M) (Nat.le_max_right _ _)))
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      intro eps heps
      obtain ⟨N,hN⟩ := hsmall eps.half heps eps.half heps
      exact ⟨N,fun m hm => lt_equiv_right (hN m hm) (Fraction.half_add_self eps)⟩

end NewtonLimitDynamics.Polygon.SweptArea
