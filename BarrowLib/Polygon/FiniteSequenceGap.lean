/-! A finite telescoping estimate for any rational-valued distance with a
zero diagonal and triangle inequality. No map or limiting premise is used.
Source of this formulation: the exact English statement and checked finite
induction below. This is project proof provenance, without historical
attribution or mathematical priority. Core Rat arithmetic is infrastructure.
The state carrier is a parameter: the proof uses no coordinates, and legacy
state callers convert only their distance values through the temporary bridge.
-/

namespace NewtonLimitDynamics.Polygon.FiniteSequenceGap
theorem finite_gap {α : Type} (D : α → α → Rat)
    (hz : ∀ s, D s s = 0)
    (htri : ∀ s t u, D s u ≤ D s t + D t u)
    (f : Nat → α) (N : Nat) (C : Rat)
    (hstep : ∀ i, i < N → D (f (i+1)) (f i) ≤ C) :
    (n k : Nat) → n+k ≤ N →
      D (f (n+k)) (f n) ≤ (k : Rat) * C
  | n, 0, _ => by simp [hz]
  | n, k+1, hnk => by
      have hp := finite_gap D hz htri f N C hstep n k (by omega)
      have hs := hstep (n+k) (by omega)
      have ht := htri (f (n+(k+1))) (f (n+k)) (f n)
      grind

end NewtonLimitDynamics.Polygon.FiniteSequenceGap
