import NewtonLimitDynamics.Polygon.GeneralForcePrecision
import BarrowLib.Polygon.CalibratedRefinement

/-! Construct fixed-time motion values from actual sampled central polygons.
The force is globally Lipschitz up to its explicit rounding error. Uniform
acceleration bounds concern actual coarse and first-half shadow arrivals;
they are not asserted globally for the harmonic law. No motion-Cauchy,
trajectory, partition-independence or derivative premise is supplied. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceEndpoint
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic ForceClasses CauchyValues
open GeneralForcePrecision

noncomputable def field (o : CentralOracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) : Point → Point :=
  o.sample (precision o.toOracle E0 hE j)

noncomputable def endpoint (o : CentralOracle) (E0 T : Fraction)
    (hE : 0 < E0.num) (s : Point × Point) (j : Nat) : Point × Point :=
  BoundedIteration.run (field o E0 hE j) (duration T j) s (blocks j)

structure Conditions (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) where
  time_nonnegative : 0 ≤ T.num
  calibration_positive : 0 < tau.num
  lipschitz : LipschitzOn o.toOracle L
  global_region : ∀ p, o.region p
  window : Fraction.le
    (Fraction.mul T (TimeCalibration.rate tau L calibration_positive)) ⟨1,2,by decide⟩
  bound_nonnegative : 0 ≤ B.num
  coarse_samples : ∀ j, BoundedIteration.BoundedSamples (field o E0 hE j)
    (Fraction.add (duration T (j+1)) (duration T (j+1))) s B (blocks j)
  shadow_samples : ∀ j k, k < blocks j → Fraction.le
    (pointNorm (field o E0 hE j
      (FiniteEstimates.cell (field o E0 hE j) (duration T (j+1))
        (FiniteAccumulation.coarseAt (field o E0 hE j) (duration T (j+1)) s k)).1)) B

noncomputable def sampleError (o : CentralOracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) : Fraction :=
  let e := o.error (precision o.toOracle E0 hE j)
  Fraction.add (Fraction.add e e) e

theorem sampleError_nonnegative (o : CentralOracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) : 0 ≤ (sampleError o E0 hE j).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_add _ _ (o.error_nonnegative _) (o.error_nonnegative _))
    (o.error_nonnegative _)

theorem cross_contract (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    FiniteEstimates.comparisonContract (field o E0 hE (j+1)) (field o E0 hE j) L
      (sampleError o E0 hE j) :=
  FiniteEstimates.comparisonContract_reverse _ _ _ _
    (samples_comparison_contract o.toOracle L d.lipschitz d.global_region
      (precision o.toOracle E0 hE j) (precision o.toOracle E0 hE (j+1))
      (precision_successor o.toOracle E0 hE j))

theorem local_contract (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    FiniteEstimates.comparisonContract (field o E0 hE j) (field o E0 hE j) L
      (sampleError o E0 hE j) :=
  samples_comparison_contract o.toOracle L d.lipschitz d.global_region _ _ (Nat.le_refl _)

def velocityCap (T B : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (pointNorm s.2) (Fraction.mul T B)

theorem velocityCap_nonnegative (T B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hB : 0 ≤ B.num) : 0 ≤ (velocityCap T B s).num :=
  Fraction.nonnegative_add _ _ (pointNorm_nonnegative _)
    (Fraction.nonnegative_mul _ _ hT hB)

theorem duration_le_window (T : Fraction) (hT : 0 ≤ T.num) (j : Nat) :
    Fraction.le (duration T j) T := by
  have hp : (1 : Int) ≤ (2 : Int)^j := by
    have hj := two_pow_ge_succ j
    have hn : (0 : Int) ≤ (j : Int) := Int.ofNat_nonneg j
    omega
  have hm := Int.mul_le_mul_of_nonneg_left hp
    (Int.mul_nonneg hT (Int.le_of_lt T.den_pos))
  simpa only [duration,Fraction.le,Int.mul_one,Int.mul_assoc] using hm

theorem fine_time (T : Fraction) (j : Nat) :
    Fraction.equiv
      (BoundedIteration.time (duration T (j+1)) (2*blocks j)) T := by
  have hn : 2*blocks j = blocks (j+1) := by rw [blocks_succ]; omega
  rw [hn]
  exact blocks_duration T (j+1)

theorem coarse_time (T : Fraction) (j : Nat) :
    Fraction.equiv
      (BoundedIteration.time
        (Fraction.add (duration T (j+1)) (duration T (j+1))) (blocks j)) T :=
  Fraction.equiv_trans
    (Fraction.mul_equiv (Fraction.equiv_refl _) (Fraction.equiv_symm (duration_halving T j)))
    (blocks_duration T j)

theorem coarse_velocity (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j k : Nat) (hk : k < blocks j) :
    Fraction.le
      (pointNorm (FiniteAccumulation.coarseAt (field o E0 hE j) (duration T (j+1)) s k).2)
      (velocityCap T B s) := by
  rw [CalibratedRefinement.coarseAt_eq_run]
  have hh : 0 ≤ (Fraction.add (duration T (j+1)) (duration T (j+1))).num :=
    Fraction.nonnegative_add _ _ d.time_nonnegative d.time_nonnegative
  have hb : BoundedIteration.BoundedSamples (field o E0 hE j)
      (Fraction.add (duration T (j+1)) (duration T (j+1))) s B k :=
    fun i hi => d.coarse_samples j i (by omega)
  have ht := Fraction.magnitudes.le_trans
    (BoundedIteration.time_monotone _ hh k (blocks j) (Nat.le_of_lt hk))
    (Fraction.le_of_equiv (coarse_time T j))
  exact BoundedIteration.velocity_bound_at_time _ _ s B T hh d.bound_nonnegative k hb ht

theorem fine_window (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    TimeCalibration.Window tau (duration T (j+1)) L d.calibration_positive (2*blocks j) := by
  have ht := Fraction.equiv_trans
    (Fraction.mul_equiv (Fraction.equiv_refl _)
      (Fraction.abs_of_nonnegative (duration T (j+1)) d.time_nonnegative)) (fine_time T j)
  exact TimeCalibration.window_of_elapsed _ _ T _ d.calibration_positive d.lipschitz.1 _
    (Fraction.le_of_equiv ht) d.window

theorem coarse_window (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    TimeCalibration.Window tau
      (Fraction.add (duration T (j+1)) (duration T (j+1))) L
      d.calibration_positive (blocks j) := by
  have hh : 0 ≤ (Fraction.add (duration T (j+1)) (duration T (j+1))).num :=
    Fraction.nonnegative_add _ _ d.time_nonnegative d.time_nonnegative
  have ht := Fraction.equiv_trans
    (Fraction.mul_equiv (Fraction.equiv_refl _) (Fraction.abs_of_nonnegative _ hh)) (coarse_time T j)
  exact TimeCalibration.window_of_elapsed _ _ T _ d.calibration_positive d.lipschitz.1 _
    (Fraction.le_of_equiv ht) d.window

/-- Derived actual adjacent comparison; the second term retains duration-representation error. -/
theorem adjacent_finite_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    Fraction.le (TimeCalibration.distance tau
      (endpoint o E0 T hE s (j+1)) (endpoint o E0 T hE s j))
      (Fraction.add
        (Fraction.mul (Fraction.ofInt (2*(blocks j : Int)))
          (CalibratedRefinement.blockSource tau (duration T (j+1)) L
            (sampleError o E0 hE j) B (velocityCap T B s) d.calibration_positive))
        (Fraction.mul (Fraction.ofInt (2*(blocks j : Int)))
          (Fraction.mul
            (Fraction.mul tau
              (Fraction.add (duration T (j+1)) (duration T (j+1))).abs)
            (sampleError o E0 hE j)))) := by
  have h1 := CalibratedRefinement.actual_uniform_error tau d.calibration_positive
    (field o E0 hE (j+1)) (field o E0 hE j) (duration T (j+1)) L (sampleError o E0 hE j)
    B (velocityCap T B s) s d.lipschitz.1 (sampleError_nonnegative o E0 hE j)
    d.bound_nonnegative (velocityCap_nonnegative T B s d.time_nonnegative d.bound_nonnegative)
    (cross_contract o E0 T tau L B s hE d j) (local_contract o E0 T tau L B s hE d j)
    (blocks j) (fine_window o E0 T tau L B s hE d j) (d.shadow_samples j)
    (fun k hk => coarse_velocity o E0 T tau L B s hE d j k hk)
  have h2 := EquivalentDuration.run_uniform_error tau d.calibration_positive
    (field o E0 hE j) (field o E0 hE j)
    (Fraction.add (duration T (j+1)) (duration T (j+1))) (duration T j) L
    (sampleError o E0 hE j) s (Fraction.equiv_symm (duration_halving T j)) d.lipschitz.1
    (sampleError_nonnegative o E0 hE j) (local_contract o E0 T tau L B s hE d j)
    (blocks j) (coarse_window o E0 T tau L B s hE d j)
  have htri := TimeCalibration.distance_triangle tau d.calibration_positive
    (FiniteAccumulation.fineAt (field o E0 hE (j+1)) (duration T (j+1)) s (blocks j))
    (FiniteAccumulation.coarseAt (field o E0 hE j) (duration T (j+1)) s (blocks j))
    (endpoint o E0 T hE s j)
  have hb := Fraction.magnitudes.le_trans htri (Fraction.add_le_add h1
    (by simpa only [CalibratedRefinement.coarseAt_eq_run] using h2))
  rw [CalibratedRefinement.fineAt_eq_run] at hb
  have hn : 2*blocks j = blocks (j+1) := by rw [blocks_succ]; omega
  rw [hn] at hb
  exact hb

/-- Both error sources have an explicit O(h)+O(force precision) endpoint bound. -/
theorem adjacent_mesh_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    Fraction.le (TimeCalibration.distance tau
      (endpoint o E0 T hE s (j+1)) (endpoint o E0 T hE s j))
      (Fraction.add
        (Fraction.mul (Fraction.mul T (duration T (j+1)))
          (CalibratedRefinement.consistencyCoefficient tau T L B (velocityCap T B s)))
        (Fraction.mul (Fraction.ofInt 7)
          (Fraction.mul (Fraction.mul tau T) (sampleError o E0 hE j)))) := by
  let h := duration T (j+1)
  let E := sampleError o E0 hE j
  let V := velocityCap T B s
  have hh : 0 ≤ h.num := d.time_nonnegative
  have hfull : 0 ≤ (Fraction.add h h).num := Fraction.nonnegative_add _ _ hh hh
  have hHT : Fraction.le h.abs T := by
    rw [Fraction.abs_eq_of_nonnegative h hh]
    exact duration_le_window T d.time_nonnegative (j+1)
  have hsmall1 : TimeCalibration.Window tau h L d.calibration_positive 1 := by
    apply TimeCalibration.window_of_elapsed _ _ T _ d.calibration_positive d.lipschitz.1 1 _ d.window
    exact Fraction.le_equiv_left (by
      simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one,Int.natCast_one]) hHT
  have hpow := TimeCalibration.amplification_power_le_two tau h L
    d.calibration_positive d.lipschitz.1 1 hsmall1
  have hK : Fraction.le (TimeCalibration.amplification tau h L d.calibration_positive)
      (Fraction.ofInt 2) := Fraction.le_equiv_left (by
    simp only [HarmonicAccumulation.fpower,Fraction.equiv,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one]) hpow
  have hsrc := CalibratedRefinement.blockSource_bound tau d.calibration_positive h T L E B V
    d.lipschitz.1 (sampleError_nonnegative o E0 hE j) d.bound_nonnegative hHT hK
  have hm := Fraction.mul_le_mul_nonnegative_left hsrc
    (Fraction.ofInt (2*(blocks j : Int))) (by dsimp [Fraction.ofInt]; omega)
  have hb := Fraction.magnitudes.le_trans (adjacent_finite_bound o E0 T tau L B s hE d j)
    (Fraction.add_le_add_right hm
      (Fraction.mul (Fraction.ofInt (2*(blocks j : Int)))
        (Fraction.mul (Fraction.mul tau (Fraction.add h h).abs) E)))
  rw [Fraction.abs_eq_of_nonnegative h hh, Fraction.abs_eq_of_nonnegative (Fraction.add h h) hfull] at hb
  apply Fraction.le_equiv_right hb
  simp only [h,E,V,blocks,duration,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.natCast_pow,Int.pow_succ,show (7 : Int) = 5+1+1 by rfl,
    Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

/-- A dimensioned acceleration precision scale remains explicit. -/
def weightedCoefficient (E0 T tau L B : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add
    (Fraction.mul (Fraction.mul T T)
      (CalibratedRefinement.consistencyCoefficient tau T L B (velocityCap T B s)))
    (Fraction.mul (Fraction.ofInt 42) (Fraction.mul (Fraction.mul tau T) E0))

theorem weightedCoefficient_nonnegative (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num)
    (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (weightedCoefficient E0 T tau L B s).num := by
  have hV := velocityCap_nonnegative T B s hT hB
  have hC : 0 ≤ (CalibratedRefinement.consistencyCoefficient tau T L B (velocityCap T B s)).num :=
    Fraction.nonnegative_add _ _ hB
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) hL)
        (Fraction.nonnegative_add _ _ hV (Fraction.nonnegative_mul _ _ hT hB)))
  exact Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hT hT) hC)
    (Fraction.nonnegative_mul _ _ (by decide)
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) hT)
        (Int.le_of_lt hE)))

/-- Geometric force precision and actual mesh consistency give a derived adjacent tail. -/
theorem adjacent_weighted_tail (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    Fraction.le (TimeCalibration.distance tau
      (endpoint o E0 T hE s (j+1)) (endpoint o E0 T hE s j))
      (GeometricTail.tailCap (weightedCoefficient E0 T tau L B s) (j+1)) := by
  have he0 := Fraction.magnitudes.lt_implies_le (precision_error o.toOracle E0 hE j)
  have he := Fraction.add_le_add (Fraction.add_le_add he0 he0) he0
  have he3 : Fraction.le (sampleError o E0 hE j)
      (Fraction.mul (Fraction.ofInt 3) (GeometricTail.tailCap E0 j)) := by
    apply Fraction.le_equiv_right he
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      show (3 : Int) = 1+1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  have hm := Fraction.mul_le_mul_nonnegative_left
    (Fraction.mul_le_mul_nonnegative_left he3 (Fraction.mul tau T)
      (Fraction.nonnegative_mul _ _ (Int.le_of_lt d.calibration_positive) d.time_nonnegative))
    (Fraction.ofInt 7) (by decide)
  have hb := Fraction.magnitudes.le_trans (adjacent_mesh_bound o E0 T tau L B s hE d j)
    (Fraction.add_le_add_left hm
      (Fraction.mul (Fraction.mul T (duration T (j+1)))
        (CalibratedRefinement.consistencyCoefficient tau T L B (velocityCap T B s))))
  apply Fraction.le_equiv_right hb
  simp only [weightedCoefficient,GeometricTail.tailCap,duration,Fraction.equiv,
    Fraction.add,Fraction.mul,Fraction.ofInt,Int.pow_succ,
    show (42 : Int) = 7*3*2 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

noncomputable def coefficient (E0 T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) (TimeCalibration.inverse tau ht))
    (weightedCoefficient E0 T tau L B s)

theorem coefficient_nonnegative (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num)
    (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (coefficient E0 T tau L B s ht).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos))
    (weightedCoefficient_nonnegative E0 T tau L B s hE hT ht hL hB)

theorem adjacent_tail (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    Fraction.le (FiniteEstimates.stateDistance
      (endpoint o E0 T hE s (j+1)) (endpoint o E0 T hE s j))
      (GeometricTail.tailCap (coefficient E0 T tau L B s d.calibration_positive) (j+1)) := by
  have hC : 0 ≤ (Fraction.add (Fraction.ofInt 1)
      (TimeCalibration.inverse tau d.calibration_positive)).num :=
    Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos)
  have hb := Fraction.magnitudes.le_trans
    (TimeCalibration.uncalibrated_le_distance tau d.calibration_positive _ _)
    (Fraction.mul_le_mul_nonnegative_left (adjacent_weighted_tail o E0 T tau L B s hE d j) _ hC)
  apply Fraction.le_equiv_right hb
  simp only [coefficient,GeometricTail.tailCap,Fraction.equiv,Fraction.mul]
  ac_nf

/-- The desired Cauchy proof is constructed from the actual adjacent recurrence. -/
noncomputable def endpointName (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE) :
    EndpointCauchyName where
  approx := endpoint o E0 T hE s
  cauchy := by
    intro eps heps
    let A := coefficient E0 T tau L B s d.calibration_positive
    have hA := coefficient_nonnegative E0 T tau L B s hE d.time_nonnegative
      d.calibration_positive d.lipschitz.1 d.bound_nonnegative
    refine ⟨GeometricTail.modulus A eps,?_⟩
    intro m n hm hn
    exact Fraction.magnitudes.lt_of_le_lt
      (GeometricTail.two_sided _ A hA (adjacent_tail o E0 T tau L B s hE d) _ m n hm hn)
      (GeometricTail.doubleTail_lt_tolerance A eps hA heps)

noncomputable def endpointValue (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE) : Value :=
  realize (endpointName o E0 T tau L B s hE d)

theorem approximants_converge (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ n, N ≤ n → Within (embed (endpoint o E0 T hE s n))
      (endpointValue o E0 T tau L B s hE d) eps :=
  constant_approximants_converge _ eps heps

theorem zero_time_endpoint (o : CentralOracle) (E0 T : Fraction)
    (hE : 0 < E0.num) (s : Point × Point) (hT : T.num = 0) (j : Nat) :
    stateEquiv (endpoint o E0 T hE s j) s :=
  BoundedIteration.zero_duration_run (field o E0 hE j) (duration T j) hT s (blocks j)

theorem zero_time_value (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (hT : T.num = 0) : endpointValue o E0 T tau L B s hE d = embed s := by
  apply Quotient.sound
  intro eps heps
  refine ⟨0,fun j _ => ?_⟩
  have hz := (distance_zero_iff_stateEquiv _ _).mpr (zero_time_endpoint o E0 T hE s hT j)
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv hz)
    ((Fraction.positive_iff_zero_lt eps).mp heps)

end NewtonLimitDynamics.Polygon.GeneralForceEndpoint
