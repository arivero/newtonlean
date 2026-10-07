import ModernLib.Foundation.Polygon.ScaledTolerance

/-! Completion of a two-input state operation whose finite distance estimate
holds on bounded position tails. The bound is data; no completed continuity
assumption is introduced. -/

namespace NewtonLimitDynamics.Polygon.BinaryLift
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic CauchyValues
open HarmonicTimeRealization

structure Operation where
  apply : (Point × Point) → (Point × Point) → (Point × Point)
  coefficient : Fraction → Fraction
  coefficient_nonnegative : ∀ R, 0 ≤ R.num → 0 ≤ (coefficient R).num
  distance_bound : ∀ (R : Fraction), 0 ≤ R.num →
    ∀ s t u v : Point × Point,
      Fraction.le (pointNorm u.1) R →
      Fraction.le (pointNorm t.1) R →
      Fraction.le (distance (apply s t) (apply u v))
        (Fraction.mul (Fraction.add (distance s u) (distance t v)) (coefficient R))

-- Modern dependency score: 1/23 (M=1, H=22; transitive project theorems/axioms).
private theorem two_small (op : Operation) (R eps : Fraction) (hR : 0 ≤ R.num)
    (s t u v : Point × Point)
    (hu : Fraction.le (pointNorm u.1) R)
    (ht : Fraction.le (pointNorm t.1) R)
    (hsu : Fraction.lt (distance s u)
      (factorDelta (op.coefficient R) eps.half (op.coefficient_nonnegative R hR)))
    (htv : Fraction.lt (distance t v)
      (factorDelta (op.coefficient R) eps.half (op.coefficient_nonnegative R hR))) :
    Fraction.lt (distance (op.apply s t) (op.apply u v)) eps := by
  have hx := factor_control (op.coefficient R) eps.half (distance s u)
    (op.coefficient_nonnegative R hR) (stateNorm_nonnegative _) hsu
  have hy := factor_control (op.coefficient R) eps.half (distance t v)
    (op.coefficient_nonnegative R hR) (stateNorm_nonnegative _) htv
  have hsmall := Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (Fraction.add_mul _ _ _))
    (lt_equiv_right (Fraction.add_lt_add hx hy)
      (Fraction.half_add_self eps))
  exact Fraction.magnitudes.lt_of_le_lt
    (op.distance_bound R hR s t u v hu ht) hsmall

def name (op : Operation) (a b : EndpointCauchyName) : EndpointCauchyName where
  approx := fun j => op.apply (a.approx j) (b.approx j)
  cauchy := by
    intro eps heps
    obtain ⟨Ra,hRa,Na,hNa⟩ := position_bounded_tail a
    obtain ⟨Rb,hRb,Nb,hNb⟩ := position_bounded_tail b
    let R := Fraction.add Ra Rb
    have hR : 0 ≤ R.num := Fraction.nonnegative_add _ _ hRa hRb
    let delta := factorDelta (op.coefficient R) eps.half (op.coefficient_nonnegative R hR)
    have hd : 0 < delta.num := factorDelta_positive _ _ _ heps
    obtain ⟨N,hN⟩ := a.cauchy delta hd
    obtain ⟨M,hM⟩ := b.cauchy delta hd
    refine ⟨max (max Na Nb) (max N M),fun i j hi hj => ?_⟩
    apply two_small op R eps hR
    · exact Fraction.magnitudes.le_trans (hNa j (by omega))
        (Fraction.le_add_nonnegative Ra Rb hRb)
    · exact Fraction.magnitudes.le_trans (hNb i (by omega))
        (Fraction.le_equiv_right (Fraction.le_add_nonnegative Rb Ra hRa) (Fraction.add_comm _ _))
    · exact hN i j (by omega) (by omega)
    · exact hM i j (by omega) (by omega)

-- Modern dependency score: 3/40 (M=3, H=37; transitive project theorems/axioms).
theorem name_equiv (op : Operation) (a b a' b' : EndpointCauchyName)
    (ha : NameEquiv a a') (hb : NameEquiv b b') :
    NameEquiv (name op a b) (name op a' b') := by
  intro eps heps
  obtain ⟨Ra,hRa,Na,hNa⟩ := position_bounded_tail a'
  obtain ⟨Rb,hRb,Nb,hNb⟩ := position_bounded_tail b
  let R := Fraction.add Ra Rb
  have hR : 0 ≤ R.num := Fraction.nonnegative_add _ _ hRa hRb
  let delta := factorDelta (op.coefficient R) eps.half (op.coefficient_nonnegative R hR)
  have hd : 0 < delta.num := factorDelta_positive _ _ _ heps
  obtain ⟨N,hN⟩ := ha delta hd
  obtain ⟨M,hM⟩ := hb delta hd
  refine ⟨max (max Na Nb) (max N M),fun j hj => ?_⟩
  apply two_small op R eps hR
  · exact Fraction.magnitudes.le_trans (hNa j (by omega))
      (Fraction.le_add_nonnegative Ra Rb hRb)
  · exact Fraction.magnitudes.le_trans (hNb j (by omega))
      (Fraction.le_equiv_right (Fraction.le_add_nonnegative Rb Ra hRa) (Fraction.add_comm _ _))
  · exact hN j (by omega)
  · exact hM j (by omega)

def value (op : Operation) (x y : Value) : Value :=
  Quotient.liftOn₂ x y (fun a b => realize (name op a b))
    (fun a b a' b' ha hb => Quotient.sound (name_equiv op a b a' b' ha hb))

-- Modern dependency score: 11/62 (M=11, H=51; transitive project theorems/axioms).
theorem value_realize (op : Operation) (a b : EndpointCauchyName) :
    value op (realize a) (realize b) = realize (name op a b) := rfl

-- Modern dependency score: 11/62 (M=11, H=51; transitive project theorems/axioms).
theorem value_embed (op : Operation) (s t : Point × Point) :
    value op (embed s) (embed t) = embed (op.apply s t) := rfl

end NewtonLimitDynamics.Polygon.BinaryLift
