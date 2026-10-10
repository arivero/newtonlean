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

-- Modern dependency score: 1/22 (M=1, H=21; transitive project theorems/axioms).
private theorem two_small (op : Operation) (R eps : Fraction) (hR : 0 ≤ R.num)
    (s t u v : Point × Point)
    (hu : Fraction.le (pointNorm u.1) R)
    (ht : Fraction.le (pointNorm t.1) R)
    (hsu : Fraction.lt (distance s u)
      (Fraction.ofRat (factorDelta ((op.coefficient R)).toRat (eps.half).toRat ((Fraction.nonnegative_iff_toRat (op.coefficient R)).mp (op.coefficient_nonnegative R hR)))))
    (htv : Fraction.lt (distance t v)
      (Fraction.ofRat (factorDelta ((op.coefficient R)).toRat (eps.half).toRat ((Fraction.nonnegative_iff_toRat (op.coefficient R)).mp (op.coefficient_nonnegative R hR))))) :
    Fraction.lt (distance (op.apply s t) (op.apply u v)) eps := by
  have hx := (show Fraction.lt (Fraction.mul ((distance s u)) ((op.coefficient R))) (eps.half) from by
      apply (Fraction.lt_iff_toRat _ _).mpr
      rw [Fraction.toRat_mul]
      have hcoef := ((Fraction.nonnegative_iff_toRat (op.coefficient R)).mp (op.coefficient_nonnegative R hR))
      have hdist := ((Fraction.nonnegative_iff_toRat (distance s u)).mp (stateNorm_nonnegative _))
      have hstrict := (Fraction.lt_iff_toRat _ _).mp hsu
      change Fraction.toRat _ < (Fraction.ofRat _).toRat at hstrict
      rw [Fraction.toRat_ofRat] at hstrict
      (try dsimp only at hcoef hdist hstrict ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff])
  have hy := (show Fraction.lt (Fraction.mul ((distance t v)) ((op.coefficient R))) (eps.half) from by
      apply (Fraction.lt_iff_toRat _ _).mpr
      rw [Fraction.toRat_mul]
      have hcoef := ((Fraction.nonnegative_iff_toRat (op.coefficient R)).mp (op.coefficient_nonnegative R hR))
      have hdist := ((Fraction.nonnegative_iff_toRat (distance t v)).mp (stateNorm_nonnegative _))
      have hstrict := (Fraction.lt_iff_toRat _ _).mp htv
      change Fraction.toRat _ < (Fraction.ofRat _).toRat at hstrict
      rw [Fraction.toRat_ofRat] at hstrict
      (try dsimp only at hcoef hdist hstrict ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff])
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
    let delta := Fraction.ofRat (factorDelta ((op.coefficient R)).toRat (eps.half).toRat ((Fraction.nonnegative_iff_toRat (op.coefficient R)).mp (op.coefficient_nonnegative R hR)))
    have hd : 0 < delta.num := (by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat (op.coefficient R)).mp (op.coefficient_nonnegative R hR))
        have hepsRat : 0 < (eps.half).toRat := (Fraction.positive_iff_toRat (eps.half)).mp heps
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos])
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

-- Modern dependency score: 3/41 (M=3, H=38; transitive project theorems/axioms).
theorem name_equiv (op : Operation) (a b a' b' : EndpointCauchyName)
    (ha : NameEquiv a a') (hb : NameEquiv b b') :
    NameEquiv (name op a b) (name op a' b') := by
  intro eps heps
  obtain ⟨Ra,hRa,Na,hNa⟩ := position_bounded_tail a'
  obtain ⟨Rb,hRb,Nb,hNb⟩ := position_bounded_tail b
  let R := Fraction.add Ra Rb
  have hR : 0 ≤ R.num := Fraction.nonnegative_add _ _ hRa hRb
  let delta := Fraction.ofRat (factorDelta ((op.coefficient R)).toRat (eps.half).toRat ((Fraction.nonnegative_iff_toRat (op.coefficient R)).mp (op.coefficient_nonnegative R hR)))
  have hd : 0 < delta.num := (by
      apply (Fraction.positive_iff_toRat _).mpr
      change 0 < (Fraction.ofRat _).toRat
      rw [Fraction.toRat_ofRat]
      have hcoef := ((Fraction.nonnegative_iff_toRat (op.coefficient R)).mp (op.coefficient_nonnegative R hR))
      have hepsRat : 0 < (eps.half).toRat := (Fraction.positive_iff_toRat (eps.half)).mp heps
      (try dsimp only at hcoef hepsRat ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos])
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

-- Modern dependency score: 11/63 (M=11, H=52; transitive project theorems/axioms).
theorem value_realize (op : Operation) (a b : EndpointCauchyName) :
    value op (realize a) (realize b) = realize (name op a b) := rfl

-- Modern dependency score: 11/63 (M=11, H=52; transitive project theorems/axioms).
theorem value_embed (op : Operation) (s t : Point × Point) :
    value op (embed s) (embed t) = embed (op.apply s t) := rfl

end NewtonLimitDynamics.Polygon.BinaryLift
