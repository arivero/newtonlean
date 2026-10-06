import ModernLib.Foundation.Polygon.ScaledTolerance

/-! Completion of uniformly coherent rational map samples on a named region.
A completed input has a regional Cauchy representative; comparisons use only
certified approximants. Representative independence is proved before choosing
a representative, without a total-map or completed-continuity premise. -/

namespace NewtonLimitDynamics.Polygon.SampledValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic CauchyValues
open HarmonicTimeRealization

structure Family where
  sample : Nat → (Point × Point) → (Point × Point)
  region : (Point × Point) → Prop
  coefficient : Fraction
  coefficient_nonnegative : 0 ≤ coefficient.num
  error : Nat → Fraction
  error_nonnegative : ∀ n, 0 ≤ (error n).num
  error_vanishes : ∀ eps : Fraction, 0 < eps.num →
    ∃ N : Nat, ∀ n, N ≤ n → Fraction.lt (error n) eps
  ordered_bound : ∀ i j, i ≤ j → ∀ s t, region s → region t →
    Fraction.le (distance (sample i s) (sample j t))
      (Fraction.add (Fraction.mul (distance s t) coefficient) (error i))

/-- Membership is witnessed by one Cauchy representative. Equivalent names
need not have every approximant in the region, especially at its boundary. -/
def Admissible (region : (Point × Point) → Prop) (x : Value) : Prop :=
  ∃ a : EndpointCauchyName, realize a = x ∧ ∀ n, region (a.approx n)

theorem admissible_realize (region : (Point × Point) → Prop)
    (a : EndpointCauchyName) (ha : ∀ n, region (a.approx n)) :
    Admissible region (realize a) := ⟨a,rfl,ha⟩

theorem admissible_embed (region : (Point × Point) → Prop) (s : Point × Point)
    (hs : region s) : Admissible region (embed s) := ⟨constantName s,rfl,fun _ => hs⟩

theorem admissible_true (x : Value) : Admissible (fun _ => True) x := by
  induction x using Quotient.inductionOn with
  | _ a => exact ⟨a,rfl,fun _ => True.intro⟩

noncomputable def admissibleName (region : (Point × Point) → Prop)
    (x : Value) (hx : Admissible region x) : EndpointCauchyName := hx.choose

theorem admissibleName_mem (region : (Point × Point) → Prop)
    (x : Value) (hx : Admissible region x) (n : Nat) :
    region ((admissibleName region x hx).approx n) := hx.choose_spec.2 n

theorem admissibleName_realize (region : (Point × Point) → Prop)
    (x : Value) (hx : Admissible region x) :
    realize (admissibleName region x hx) = x := hx.choose_spec.1

theorem scaled_add_small (C eps d e : Fraction) (hC : 0 ≤ C.num)
    (hd : 0 ≤ d.num)
    (hdelta : Fraction.lt d (factorDelta C eps.half hC))
    (he : Fraction.lt e eps.half) :
    Fraction.lt (Fraction.add (Fraction.mul d C) e) eps :=
  lt_equiv_right (Fraction.add_lt_add
    (factor_control C eps.half d hC hd hdelta) he) (Fraction.half_add_self eps)

def sampledName (f : Family) (a : EndpointCauchyName)
    (ha : ∀ n, f.region (a.approx n)) : EndpointCauchyName where
  approx := fun n => f.sample n (a.approx n)
  cauchy := by
    intro eps heps
    let delta := factorDelta f.coefficient eps.half f.coefficient_nonnegative
    obtain ⟨N,hN⟩ := a.cauchy delta (factorDelta_positive _ _ _ heps)
    obtain ⟨M,hM⟩ := f.error_vanishes eps.half heps
    refine ⟨max N M,fun i j hi hj => ?_⟩
    by_cases hij : i ≤ j
    · exact Fraction.magnitudes.lt_of_le_lt (f.ordered_bound i j hij _ _ (ha i) (ha j))
        (scaled_add_small _ eps _ _ f.coefficient_nonnegative (stateNorm_nonnegative _)
          (hN i j (by omega) (by omega)) (hM i (by omega)))
    · have hji : j ≤ i := by omega
      exact Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_equiv_left (stateSub_norm_symm _ _) (f.ordered_bound j i hji _ _ (ha j) (ha i)))
        (scaled_add_small _ eps _ _ f.coefficient_nonnegative (stateNorm_nonnegative _)
          (hN j i (by omega) (by omega)) (hM j (by omega)))

theorem sampledName_equiv (f : Family) (a b : EndpointCauchyName)
    (ha : ∀ n, f.region (a.approx n)) (hb : ∀ n, f.region (b.approx n))
    (hab : NameEquiv a b) : NameEquiv (sampledName f a ha) (sampledName f b hb) := by
  intro eps heps
  let delta := factorDelta f.coefficient eps.half f.coefficient_nonnegative
  obtain ⟨N,hN⟩ := hab delta (factorDelta_positive _ _ _ heps)
  obtain ⟨M,hM⟩ := f.error_vanishes eps.half heps
  refine ⟨max N M,fun n hn => ?_⟩
  exact Fraction.magnitudes.lt_of_le_lt (f.ordered_bound n n (Nat.le_refl _) _ _ (ha n) (hb n))
    (scaled_add_small _ eps _ _ f.coefficient_nonnegative (stateNorm_nonnegative _)
      (hN n (by omega)) (hM n (by omega)))

/-- The existing completed operation is restricted to certified inputs. The
name-equivalence theorem proves that the chosen regional representative does
not change its output. No second completed domain or total extension is built. -/
noncomputable def sampledValue (f : Family) (x : Value)
    (hx : Admissible f.region x) : Value :=
  realize (sampledName f (admissibleName f.region x hx) (admissibleName_mem f.region x hx))

theorem sampledValue_realize (f : Family) (a : EndpointCauchyName)
    (ha : ∀ n, f.region (a.approx n)) (hx : Admissible f.region (realize a)) :
    sampledValue f (realize a) hx = realize (sampledName f a ha) := by
  apply Quotient.sound
  exact sampledName_equiv f _ a (admissibleName_mem _ _ hx) ha
    (Quotient.exact (admissibleName_realize _ _ hx))

theorem sampledValue_congr (f : Family) (x y : Value)
    (hx : Admissible f.region x) (hy : Admissible f.region y) (hxy : x=y) :
    sampledValue f x hx = sampledValue f y hy := by
  cases hxy
  rfl

def offsetFamily (f : Family) (m : Nat) : Family where
  region := f.region
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

theorem sampledName_offset_equiv (f : Family) (a : EndpointCauchyName)
    (ha : ∀ n, f.region (a.approx n)) (m : Nat) :
    NameEquiv (sampledName f a ha) (sampledName (offsetFamily f m) a ha) := by
  intro eps heps
  obtain ⟨N,hN⟩ := f.error_vanishes eps heps
  refine ⟨N,fun j hj => ?_⟩
  have hc := f.ordered_bound j (m+j) (by omega) (a.approx j) (a.approx j) (ha j) (ha j)
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

theorem sampledValue_offset (f : Family) (x : Value)
    (hx : Admissible f.region x) (m : Nat) :
    sampledValue (offsetFamily f m) x hx = sampledValue f x hx :=
  Quotient.sound (nameEquiv_symm (sampledName_offset_equiv f _
    (admissibleName_mem _ _ hx) m))

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

theorem sampledValue_within (f : Family) (x y : Value)
    (hx : Admissible f.region x) (hy : Admissible f.region y)
    (R : Fraction) (hxy : Within x y R) :
    Within (sampledValue f x hx) (sampledValue f y hy) (Fraction.mul R f.coefficient) := by
  let a := admissibleName f.region x hx
  let b := admissibleName f.region y hy
  have hab : NameBound a b R := by
    change Within (realize a) (realize b) R
    simpa only [a,b,admissibleName_realize] using hxy
  exact nameBound_scale_error _ _ a b _ R f.coefficient_nonnegative f.error
    f.error_vanishes (fun n => f.ordered_bound n n (Nat.le_refl _) _ _
      (admissibleName_mem _ _ hx n) (admissibleName_mem _ _ hy n)) hab

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
    (ha : ∀ n, f.region (a.approx n)) (hx : Admissible f.region (realize a))
    (m : Nat) (R : Fraction) (hnear : Within (embed (a.approx m)) (realize a) R) :
    Within (embed (f.sample m (a.approx m))) (sampledValue f (realize a) hx)
      (Fraction.add (Fraction.mul R f.coefficient) (f.error m)) := by
  rw [sampledValue_realize f a ha hx]
  exact nameBound_affine _ _ (constantName (a.approx m)) a _ R _
    f.coefficient_nonnegative m
    (fun n hn => f.ordered_bound m n hn _ _ (ha m) (ha n)) hnear

end NewtonLimitDynamics.Polygon.SampledValues
