import BarrowLib.Polygon.ScaledTolerance

/-! Completion of uniformly coherent rational map samples. Cauchy values and
representative independence are derived from finite comparisons and vanishing
error; neither a completed map nor continuity of that map is supplied. -/

namespace NewtonLimitDynamics.Polygon.SampledValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic CauchyValues
open HarmonicTimeRealization

structure Family where
  sample : Nat → (Point × Point) → (Point × Point)
  coefficient : Fraction
  coefficient_nonnegative : 0 ≤ coefficient.num
  error : Nat → Fraction
  error_nonnegative : ∀ n, 0 ≤ (error n).num
  error_vanishes : ∀ eps : Fraction, 0 < eps.num →
    ∃ N : Nat, ∀ n, N ≤ n → Fraction.lt (error n) eps
  ordered_bound : ∀ i j, i ≤ j → ∀ s t,
    Fraction.le (distance (sample i s) (sample j t))
      (Fraction.add (Fraction.mul (distance s t) coefficient) (error i))

theorem scaled_add_small (C eps d e : Fraction) (hC : 0 ≤ C.num)
    (hd : 0 ≤ d.num)
    (hdelta : Fraction.lt d (factorDelta C eps.half hC))
    (he : Fraction.lt e eps.half) :
    Fraction.lt (Fraction.add (Fraction.mul d C) e) eps :=
  lt_equiv_right (Fraction.add_lt_add
    (factor_control C eps.half d hC hd hdelta) he) (Fraction.half_add_self eps)

def sampledName (f : Family) (a : EndpointCauchyName) : EndpointCauchyName where
  approx := fun n => f.sample n (a.approx n)
  cauchy := by
    intro eps heps
    let delta := factorDelta f.coefficient eps.half f.coefficient_nonnegative
    obtain ⟨N,hN⟩ := a.cauchy delta (factorDelta_positive _ _ _ heps)
    obtain ⟨M,hM⟩ := f.error_vanishes eps.half heps
    refine ⟨max N M,fun i j hi hj => ?_⟩
    by_cases hij : i ≤ j
    · exact Fraction.magnitudes.lt_of_le_lt (f.ordered_bound i j hij _ _)
        (scaled_add_small _ eps _ _ f.coefficient_nonnegative (stateNorm_nonnegative _)
          (hN i j (by omega) (by omega)) (hM i (by omega)))
    · have hji : j ≤ i := by omega
      exact Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_equiv_left (stateSub_norm_symm _ _) (f.ordered_bound j i hji _ _))
        (scaled_add_small _ eps _ _ f.coefficient_nonnegative (stateNorm_nonnegative _)
          (hN j i (by omega) (by omega)) (hM j (by omega)))

theorem sampledName_equiv (f : Family) (a b : EndpointCauchyName)
    (hab : NameEquiv a b) : NameEquiv (sampledName f a) (sampledName f b) := by
  intro eps heps
  let delta := factorDelta f.coefficient eps.half f.coefficient_nonnegative
  obtain ⟨N,hN⟩ := hab delta (factorDelta_positive _ _ _ heps)
  obtain ⟨M,hM⟩ := f.error_vanishes eps.half heps
  refine ⟨max N M,fun n hn => ?_⟩
  exact Fraction.magnitudes.lt_of_le_lt (f.ordered_bound n n (Nat.le_refl _) _ _)
    (scaled_add_small _ eps _ _ f.coefficient_nonnegative (stateNorm_nonnegative _)
      (hN n (by omega)) (hM n (by omega)))

def sampledValue (f : Family) : Value → Value :=
  Quotient.lift (fun a => realize (sampledName f a))
    (fun a b h => Quotient.sound (sampledName_equiv f a b h))

theorem sampledValue_realize (f : Family) (a : EndpointCauchyName) :
    sampledValue f (realize a) = realize (sampledName f a) := rfl

def offsetFamily (f : Family) (m : Nat) : Family where
  sample := fun j => f.sample (m+j)
  coefficient := f.coefficient
  coefficient_nonnegative := f.coefficient_nonnegative
  error := fun j => f.error (m+j)
  error_nonnegative := fun j => f.error_nonnegative (m+j)
  error_vanishes := by
    intro eps heps
    obtain ⟨N,hN⟩ := f.error_vanishes eps heps
    exact ⟨N,fun j hj => hN (m+j) (by omega)⟩
  ordered_bound := fun i j hij => f.ordered_bound (m+i) (m+j) (by omega)

theorem sampledName_offset_equiv (f : Family) (a : EndpointCauchyName) (m : Nat) :
    NameEquiv (sampledName f a) (sampledName (offsetFamily f m) a) := by
  intro eps heps
  obtain ⟨N,hN⟩ := f.error_vanishes eps heps
  refine ⟨N,fun j hj => ?_⟩
  have hc := f.ordered_bound j (m+j) (by omega) (a.approx j) (a.approx j)
  have hz : Fraction.equiv
      (Fraction.add (Fraction.mul (distance (a.approx j) (a.approx j)) f.coefficient) (f.error j))
      (f.error j) := by
    apply Fraction.equiv_trans (Fraction.add_equiv
      (Fraction.mul_equiv (HarmonicAccumulation.stateSub_self_norm_zero _) (Fraction.equiv_refl _))
      (Fraction.equiv_refl _))
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.zero_mul,Int.mul_zero,Int.zero_add,Int.mul_one,Int.one_mul]
    ac_nf
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_equiv_right hc hz) (hN j hj)

theorem sampledValue_offset (f : Family) (x : Value) (m : Nat) :
    sampledValue (offsetFamily f m) x = sampledValue f x := by
  induction x using Quotient.inductionOn with
  | _ a => exact Quotient.sound (nameEquiv_symm (sampledName_offset_equiv f a m))

theorem nameBound_of_vanishing_error (a b : EndpointCauchyName) (R : Fraction)
    (e : Nat → Fraction)
    (he : ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ n, N≤n → Fraction.lt (e n) eps)
    (hlevel : ∀ n, Fraction.le (distance (a.approx n) (b.approx n)) (Fraction.add R (e n))) :
    NameBound a b R := by
  intro eps heps
  obtain ⟨N,hN⟩ := he eps heps
  exact ⟨N,fun n hn => Fraction.magnitudes.lt_of_le_lt (hlevel n)
    (CauchyValues.add_lt_add_left (hN n hn) R)⟩

theorem nameBound_scale_error (a b ta tb : EndpointCauchyName)
    (C R : Fraction) (hC : 0 ≤ C.num) (e : Nat → Fraction)
    (he : ∀ eps : Fraction, 0 < eps.num →
      ∃ N : Nat, ∀ n, N ≤ n → Fraction.lt (e n) eps)
    (hlevel : ∀ n, Fraction.le (distance (a.approx n) (b.approx n))
      (Fraction.add (Fraction.mul (distance (ta.approx n) (tb.approx n)) C) (e n)))
    (hnear : NameBound ta tb R) : NameBound a b (Fraction.mul R C) := by
  intro eps heps
  let q := eps.half.half
  let delta := factorDelta C q hC
  obtain ⟨N,hN⟩ := hnear delta (factorDelta_positive _ _ _ heps)
  obtain ⟨M,hM⟩ := he q heps
  refine ⟨max N M,fun n hn => ?_⟩
  have hm := Fraction.mul_le_mul_nonnegative
    (Fraction.magnitudes.lt_implies_le (hN n (by omega))) C hC
  have hs := Fraction.le_equiv_right hm (Fraction.add_mul R delta C)
  have hd := factor_delta_weak C q hC (Int.le_of_lt heps)
  have hb := Fraction.magnitudes.le_trans (hlevel n)
    (Fraction.add_le_add (Fraction.magnitudes.le_trans hs
      (Fraction.add_le_add_left hd (Fraction.mul R C)))
      (Fraction.magnitudes.lt_implies_le (hM n (by omega))))
  have hc : Fraction.equiv
      (Fraction.add (Fraction.add (Fraction.mul R C) q) q)
      (Fraction.add (Fraction.mul R C) eps.half) :=
    Fraction.equiv_trans (Fraction.add_assoc _ _ _)
      (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.half_add_self eps.half))
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_equiv_right hb hc)
    (CauchyValues.add_lt_add_left (Fraction.half_lt eps heps) _)

theorem sampledValue_within (f : Family) (x y : Value) (R : Fraction)
    (hxy : Within x y R) :
    Within (sampledValue f x) (sampledValue f y) (Fraction.mul R f.coefficient) := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      exact nameBound_scale_error _ _ a b _ R f.coefficient_nonnegative f.error
        f.error_vanishes (fun n => f.ordered_bound n n (Nat.le_refl _) _ _) hxy

theorem nameBound_affine (a b ta tb : EndpointCauchyName)
    (C R E : Fraction) (hC : 0 ≤ C.num) (M : Nat)
    (hlevel : ∀ n, M ≤ n → Fraction.le (distance (a.approx n) (b.approx n))
      (Fraction.add (Fraction.mul (distance (ta.approx n) (tb.approx n)) C) E))
    (hnear : NameBound ta tb R) :
    NameBound a b (Fraction.add (Fraction.mul R C) E) := by
  intro eps heps
  let delta := factorDelta C eps.half hC
  obtain ⟨N,hN⟩ := hnear delta (factorDelta_positive _ _ _ heps)
  refine ⟨max N M,fun n hn => ?_⟩
  have hm := Fraction.mul_le_mul_nonnegative
    (Fraction.magnitudes.lt_implies_le (hN n (by omega))) C hC
  have hs := Fraction.le_equiv_right hm (Fraction.add_mul R delta C)
  have hd := factor_delta_weak C eps.half hC (Int.le_of_lt heps)
  have hb := Fraction.magnitudes.le_trans (hlevel n (by omega))
    (Fraction.add_le_add_right (Fraction.magnitudes.le_trans hs
      (Fraction.add_le_add_left hd (Fraction.mul R C))) E)
  have hc : Fraction.equiv
      (Fraction.add (Fraction.add (Fraction.mul R C) eps.half) E)
      (Fraction.add (Fraction.add (Fraction.mul R C) E) eps.half) := by
    simp only [Fraction.equiv,Fraction.add,Int.add_mul,Int.mul_add]
    ac_nf
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_equiv_right hb hc)
    (CauchyValues.add_lt_add_left (Fraction.half_lt eps heps) _)

theorem sampled_approximant_bound (f : Family) (a : EndpointCauchyName)
    (m : Nat) (R : Fraction) (hnear : Within (embed (a.approx m)) (realize a) R) :
    Within (embed (f.sample m (a.approx m))) (sampledValue f (realize a))
      (Fraction.add (Fraction.mul R f.coefficient) (f.error m)) :=
  nameBound_affine _ _ (constantName (a.approx m)) a _ R _
    f.coefficient_nonnegative m
    (fun n hn => f.ordered_bound m n hn _ _) hnear

end NewtonLimitDynamics.Polygon.SampledValues
