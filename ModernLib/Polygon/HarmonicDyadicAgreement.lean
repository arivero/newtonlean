import ModernLib.Foundation.Polygon.FiniteAddress
import ModernLib.Polygon.HarmonicIntegerSubdivision
import ModernLib.Polygon.HarmonicConstructionAgreement
import ModernLib.Foundation.Polygon.IntegerTime

/-! E/G agreement at every finite binary dyadic time, from an actual
integer-subdivision comparison whose error decreases geometrically. -/

namespace NewtonLimitDynamics.Polygon.HarmonicConstructionAgreement
open NewtonLimitDynamics TimeSubdivision CentralSchedule HarmonicStability
open HarmonicDyadic HarmonicBinaryPrefix HarmonicComparison PointBounds
open HarmonicTimeComparison HarmonicTimeRealization HarmonicAccumulation
open IntegerSchedule FiniteRecurrence BinaryTime CauchyValues HarmonicIntegerSubdivision

-- Modern dependency score: 7/30 (M=7, H=23; transitive project theorems/axioms).
theorem timeApprox_small (b : Nat → Bool) (w T : Fraction) (m : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    DyadicSmallTime w (timeApprox b T m) := by
  have ht := prefix_elapsed_le_time b T m hT
  have hp := Fraction.le_equiv_left (Fraction.equiv_symm (prefix_elapsed b T m)) ht
  exact Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative hp (Fraction.add (Fraction.ofInt 1) w.abs)
      (Fraction.nonnegative_add _ _ (by decide) (Fraction.abs_num_nonnegative w))) hs

-- Modern dependency score: 10/38 (M=10, H=28; transitive project theorems/axioms).
theorem dyadic_integer_small (b : Nat → Bool) (w T : Fraction) (m j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    FullSmallTime w (integerDuration (duration T (m+j)) (ticks b m)) (blocks j) := by
  have hd := Fraction.mul_equiv (dyadic_fullTime b T m j)
    (Fraction.equiv_refl (Fraction.add (Fraction.ofInt 1) w.abs))
  exact Fraction.le_equiv_left hd (timeApprox_small b w T m hT hs)

def dyadicIntegerCoefficient (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt 4)
    (Fraction.mul (Fraction.mul (duration T m) (duration T m))
      (quadraticCap w s (ticks b m)))

-- Modern dependency score: 3/8 (M=3, H=5; transitive project theorems/axioms).
theorem dyadicIntegerCoefficient_nonnegative (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m : Nat) (hT : 0 ≤ T.num) :
    0 ≤ (dyadicIntegerCoefficient b w T s m).num :=
  Fraction.nonnegative_mul _ _ (by decide)
    (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hT hT)
      (quadraticCap_nonnegative w s (ticks b m)))

-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
theorem dyadic_integer_error_cap (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m j : Nat) :
    Fraction.equiv
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (Fraction.ofInt (blocks j:Int))
          (blockSource w (duration T (m+j)) (ticks b m) s)))
      (duration (dyadicIntegerCoefficient b w T s m) j) := by
  have hb : (blocks j:Int)=(2:Int)^j := by
    simp only [blocks,Int.natCast_pow]
    rfl
  simp only [blockSource,dyadicIntegerCoefficient,duration,hb,
    Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_pow,
    FiniteGrowth.denominator_power_add]
  simp only [show (4:Int)=2*2 by rfl]
  ac_nf

-- Modern dependency score: 3/6 (M=3, H=3; transitive project theorems/axioms).
theorem dyadic_fine_prefix (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m j : Nat) (hz : ∀ i, m ≤ i → b i = false) :
    fineBlocks w (duration T (m+j)) (ticks b m) s (blocks j) =
      prefixState b w T s (m+j) := by
  rw [fineBlocks_eq_schedule]
  simp only [integerFine,prefixState,ticks_zero_tail b m hz j]

-- Modern dependency score: 6/20 (M=6, H=14; transitive project theorems/axioms).
theorem dyadic_coarse_endpoint (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m j : Nat) :
    stateEquiv
      (coarseBlocks w (duration T (m+j)) (ticks b m) s (blocks j))
      (endpoint w (timeApprox b T m) s j) := by
  rw [coarseBlocks_eq_schedule]
  exact schedule_replicate_congr w _ _ (dyadic_integer_duration b T m j)
    (blocks j) s s ⟨⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

-- Modern dependency score: 81/187 (M=81, H=106; transitive project theorems/axioms).
theorem finite_tail_level_error (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hk : 0 < ticks b m) (hz : ∀ i, m ≤ i → b i = false) :
    Fraction.le
      (distance (endpoint w (timeApprox b T m) s j) (prefixState b w T s (m+j)))
      (duration (dyadicIntegerCoefficient b w T s m) j) := by
  have hi := accumulated_integer_error_positive w (duration T (m+j))
    (ticks b m) (blocks j) s hT hk (Nat.pow_pos (by decide))
    (dyadic_integer_small b w T m j hT hs)
  rw [dyadic_fine_prefix b w T s m j hz] at hi
  have he : Fraction.equiv
      (distance (prefixState b w T s (m+j))
        (coarseBlocks w (duration T (m+j)) (ticks b m) s (blocks j)))
      (distance (prefixState b w T s (m+j)) (endpoint w (timeApprox b T m) s j)) :=
    stateNorm_equiv (stateSub_congr
      ⟨⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,
        ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩
      (dyadic_coarse_endpoint b w T s m j))
  exact Fraction.le_equiv_left (stateSub_norm_symm _ _)
    (Fraction.le_equiv_right
      (Fraction.le_equiv_left (Fraction.equiv_symm he) hi)
      (dyadic_integer_error_cap b w T s m j))

-- Modern dependency score: 166/281 (M=166, H=115; transitive project theorems/axioms).
theorem finite_tail_names (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hz : ∀ i, m ≤ i → b i = false) :
    NameEquiv
      (endpointName w (timeApprox b T m) s (timeApprox_nonnegative b T m hT)
        (timeApprox_small b w T m hT hs)) (prefixName b w T s hT hs) := by
  by_cases hk : ticks b m = 0
  · have ht : (timeApprox b T m).num = 0 := by simp only [timeApprox,Fraction.mul,
        Fraction.ofInt,hk,Int.natCast_zero,Int.zero_mul]
    intro eps heps
    refine ⟨m, ?_⟩
    intro j hj
    have he := zero_time_endpoint w (timeApprox b T m) s j ht
    have hindex : m+(j-m)=j := by omega
    have hp : prefixState b w T s j = s := by
      rw [← hindex]
      simp only [prefixState,ticks_zero_tail b m hz (j-m),hk,Nat.zero_mul,
        List.replicate_zero,schedule]
    have heq : Fraction.equiv
        (distance (endpoint w (timeApprox b T m) s j) (prefixState b w T s j))
        (distance s s) := by
      rw [hp]
      exact stateNorm_equiv (stateSub_congr he
        ⟨⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,
          ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩)
    exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv heq)
      (distance_self_lt s eps heps)
  · have hkpos : 0 < ticks b m := by omega
    intro eps heps
    obtain ⟨N,hN⟩ := duration_eventually_small (dyadicIntegerCoefficient b w T s m)
      eps.half.half (dyadicIntegerCoefficient_nonnegative b w T s m hT) heps
    obtain ⟨K,hK⟩ := (prefixName b w T s hT hs).cauchy eps.half.half heps
    refine ⟨N+K, ?_⟩
    intro j hj
    have herror := Fraction.magnitudes.lt_of_le_lt
      (finite_tail_level_error b w T s m j hT hs hkpos hz) (hN j (by omega))
    have hshift := hK (m+j) j (by omega) (by omega)
    have htri := stateSub_triangle (endpoint w (timeApprox b T m) s j)
      (prefixState b w T s (m+j)) (prefixState b w T s j)
    have hsum := Fraction.add_le_add (Fraction.magnitudes.lt_implies_le herror)
      (Fraction.magnitudes.lt_implies_le hshift)
    have hbound := Fraction.le_equiv_right (Fraction.magnitudes.le_trans htri hsum)
      (Fraction.half_add_self eps.half)
    exact Fraction.magnitudes.lt_of_le_lt hbound (Fraction.half_lt eps heps)

/-- Every finite binary dyadic time has the same completed state under the
endpoint and one-global-family prefix constructions. -/
-- Modern dependency score: 191/313 (M=191, H=122; transitive project theorems/axioms).
theorem finite_tail_value (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hz : ∀ i, m ≤ i → b i = false) :
    CauchyValues.timeValue w s
      ⟨timeApprox b T m,timeApprox_nonnegative b T m hT,timeApprox_small b w T m hT hs⟩ =
      gammaValue w T s hT hs (Quotient.mk _ b) :=
  Quotient.sound (finite_tail_names b w T s m hT hs hz)

def dyadicTime (w T : Fraction) (k m : Nat) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (_hk : k<blocks m) : ShortRationalTime w :=
  ⟨timeApprox (finiteAddress m k) T m,
    timeApprox_nonnegative (finiteAddress m k) T m hT,
    timeApprox_small (finiteAddress m k) w T m hT hs⟩

-- Modern dependency score: 11/35 (M=11, H=24; transitive project theorems/axioms).
theorem dyadicTime_exact (w T : Fraction) (k m : Nat) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (hk : k<blocks m) :
    (dyadicTime w T k m hT hs hk).val =
      Fraction.mul (Fraction.ofInt (k:Int)) (duration T m) := by
  simp only [dyadicTime,timeApprox,finiteAddress_ticks m k hk]

/-- Every numerator below 2^m has an explicitly constructed address;
agreement does not assume a representation exists. The full endpoint uses
full_window_value. -/
-- Modern dependency score: 193/315 (M=193, H=122; transitive project theorems/axioms).
theorem dyadic_value (w T : Fraction) (s : Point × Point) (k m : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (hk : k<blocks m) :
    CauchyValues.timeValue w s (dyadicTime w T k m hT hs hk) =
      gammaValue w T s hT hs (Quotient.mk _ (finiteAddress m k)) :=
  finite_tail_value (finiteAddress m k) w T s m hT hs (finiteAddress_tail m k)

-- Modern dependency score: 82/171 (M=82, H=89; transitive project theorems/axioms).
theorem timeValue_equiv_parameter (w : Fraction) (s : Point × Point)
    (t u : ShortRationalTime w) (ht : Fraction.equiv t.val u.val) :
    CauchyValues.timeValue w s t = CauchyValues.timeValue w s u := by
  apply Quotient.sound
  apply nameEquiv_of_levelwise_stateEquiv
  intro j
  exact schedule_replicate_congr w _ _ (duration_congr ht j) (blocks j) s s
    ⟨⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

-- Modern dependency score: 146/250 (M=146, H=104; transitive project theorems/axioms).
theorem full_dyadic_value_at_represented_time (w T : Fraction) (s : Point × Point)
    (m : Nat) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (t : ShortRationalTime w)
    (ht : Fraction.equiv t.val
      (Fraction.mul (Fraction.ofInt (blocks m:Int)) (duration T m))) :
    CauchyValues.timeValue w s t = gammaValue w T s hT hs (rightTime T hT) :=
  (timeValue_equiv_parameter w s t ⟨T,hT,hs⟩
    (Fraction.equiv_trans ht (blocks_duration T m))).trans
    (full_window_value w T s hT hs)

-- Modern dependency score: 199/322 (M=199, H=123; transitive project theorems/axioms).
theorem dyadic_value_at_represented_time (w T : Fraction) (s : Point × Point)
    (k m : Nat) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (hk : k<blocks m) (t : ShortRationalTime w)
    (ht : Fraction.equiv t.val
      (Fraction.mul (Fraction.ofInt (k:Int)) (duration T m))) :
    CauchyValues.timeValue w s t =
      gammaValue w T s hT hs (Quotient.mk _ (finiteAddress m k)) := by
  have he : Fraction.equiv t.val (dyadicTime w T k m hT hs hk).val := by
    rw [dyadicTime_exact w T k m hT hs hk]
    exact ht
  exact (timeValue_equiv_parameter w s t (dyadicTime w T k m hT hs hk) he).trans
    (dyadic_value w T s k m hT hs hk)

/-- A three-tick time has equal completed values even though the earlier
exact control proves its finite endpoint and prefix schedules unequal. -/
-- Modern dependency score: 194/316 (M=194, H=122; transitive project theorems/axioms).
theorem three_tick_value_agreement (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    CauchyValues.timeValue w s (dyadicTime w T 3 2 hT hs (by decide)) =
      gammaValue w T s hT hs (Quotient.mk _ (finiteAddress 2 3)) :=
  dyadic_value w T s 3 2 hT hs (by decide)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem three_tick_address_control :
    ticks (finiteAddress 2 3) 2 = 3 ∧
      finiteAddress 2 3 2 = false ∧ finiteAddress 2 3 5 = false := by decide

end NewtonLimitDynamics.Polygon.HarmonicConstructionAgreement
