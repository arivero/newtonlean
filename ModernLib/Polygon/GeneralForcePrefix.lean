import ModernLib.Polygon.GeneralForceEndpoint
import ModernLib.Foundation.Polygon.BinaryTime

/-! Actual prefixes of one dyadic sampled central-force family. The Cauchy
estimate is derived from paired refinement and the actual optional cell. Force
bounds are on the represented runs, and no motion-name premise is supplied. -/

namespace NewtonLimitDynamics.Polygon.GeneralForcePrefix
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix ForceClasses CauchyValues
open GeneralForceEndpoint

structure Conditions (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    extends GeneralForceEndpoint.Conditions o E0 T tau L B s hE where
namespace Conditions
variable {o : CentralOracle} {E0 T tau L B : Fraction} {s : Point × Point} {hE : 0 < E0.num}

-- Modern dependency score: 14/63 (M=14, H=49; transitive project theorems/axioms).
theorem actual_samples (d : Conditions o E0 T tau L B s hE) (j : Nat) :
    BoundedIteration.BoundedSamples (field o E0 hE j) (duration T j) s B (blocks j) :=
  d.toConditions.actual_samples j

end Conditions

noncomputable def countState (o : CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (j n : Nat) : Point × Point :=
  BoundedIteration.run (field o E0 hE j) (duration T j) s n

noncomputable def prefixState (b : Nat → Bool) (o : CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (j : Nat) : Point × Point :=
  countState o E0 T s hE j (ticks b j)

-- Modern dependency score: 0/9 (M=0, H=9; transitive project theorems/axioms).
theorem count_time_le (T : Fraction) (hT : 0 ≤ T.num) (j n : Nat) (hn : n ≤ blocks j) :
    Fraction.le (BoundedIteration.time (duration T j) n) T :=
  Fraction.magnitudes.le_trans
    (BoundedIteration.time_monotone (duration T j) hT n (blocks j) hn)
    (Fraction.le_of_equiv (blocks_duration T j))

-- Modern dependency score: 16/67 (M=16, H=51; transitive project theorems/axioms).
theorem count_velocity (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j n : Nat) (hn : n ≤ blocks j) :
    Fraction.le (pointNorm (countState o E0 T s hE j n).2) (velocityCap T B s) :=
  BoundedIteration.velocity_bound_at_time (field o E0 hE j) (duration T j) s B T
    d.time_nonnegative d.bound_nonnegative
    n (fun i hi => d.actual_samples j i (by omega))
    (count_time_le T d.time_nonnegative j n hn)

-- Modern dependency score: 15/64 (M=15, H=49; transitive project theorems/axioms).
theorem count_region (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j n : Nat) (hn : n ≤ blocks j) : o.region (countState o E0 T s hE j n).1 :=
  d.toConditions.run_region j (duration T j) d.time_nonnegative n
    (count_time_le T d.time_nonnegative j n hn)

/-- Every restarted comparison uses two certified points of the original run. -/
-- Modern dependency score: 20/74 (M=20, H=54; transitive project theorems/axioms).
theorem restarted_comparison (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j n k : Nat) (hn : n+k ≤ blocks j) (i : Nat) (hi : i<k) :
    Fraction.le (FiniteEstimates.pointDistance
      (field o E0 hE j (BoundedIteration.run (field o E0 hE j) (duration T j)
        (countState o E0 T s hE j n) (i+1)).1)
      (field o E0 hE j (countState o E0 T s hE j n).1))
      (Fraction.add (Fraction.mul L (FiniteEstimates.pointDistance
        (BoundedIteration.run (field o E0 hE j) (duration T j)
          (countState o E0 T s hE j n) (i+1)).1
        (countState o E0 T s hE j n).1)) (sampleError o E0 hE j)) := by
  apply local_contract o E0 T tau L B s hE d.toConditions j _ _ _
    (count_region o E0 T tau L B s hE d j n (by omega))
  change o.region (BoundedIteration.run (field o E0 hE j) (duration T j)
    (BoundedIteration.run (field o E0 hE j) (duration T j) s n) (i+1)).1
  rw [← BoundedIteration.run_add]
  exact count_region o E0 T tau L B s hE d j (n+(i+1)) (by omega)

def speedCap (T tau B : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (velocityCap T B s) (Fraction.mul tau B)

-- Modern dependency score: 1/5 (M=1, H=4; transitive project theorems/axioms).
theorem speedCap_nonnegative (T tau B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hB : 0 ≤ B.num) :
    0 ≤ (speedCap T tau B s).num :=
  Fraction.nonnegative_add _ _ (velocityCap_nonnegative T B s hT hB)
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) hB)

/-- Every increment samples the actual arrival of the represented family. -/
-- Modern dependency score: 17/73 (M=17, H=56; transitive project theorems/axioms).
theorem count_step_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j n : Nat) (hn : n < blocks j) :
    Fraction.le (TimeCalibration.distance tau (countState o E0 T s hE j (n+1))
      (countState o E0 T s hE j n))
      (Fraction.mul (duration T j) (speedCap T tau B s)) := by
  have hb := TimeCalibration.cell_increment_bound tau (duration T j) B
    (velocityCap T B s) (field o E0 hE j) (countState o E0 T s hE j n)
    (Int.le_of_lt d.calibration_positive) (count_velocity o E0 T tau L B s hE d j n (Nat.le_of_lt hn))
    (d.actual_samples j n hn)
  rw [Fraction.abs_eq_of_nonnegative (duration T j) d.time_nonnegative] at hb
  exact hb

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem prefix_next (b : Nat → Bool) (o : CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (j : Nat) :
    prefixState b o E0 T s hE (j+1) =
      if b j then countState o E0 T s hE (j+1) (2*ticks b j+1)
      else countState o E0 T s hE (j+1) (2*ticks b j) := by
  simp only [prefixState,ticks,bit]
  split <;> rfl

def weightedCoefficient (E0 T tau L B : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (GeneralForceEndpoint.weightedCoefficient E0 T tau L B s)
    (Fraction.mul T (speedCap T tau B s))

-- Modern dependency score: 3/7 (M=3, H=4; transitive project theorems/axioms).
theorem weightedCoefficient_nonnegative (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num)
    (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (weightedCoefficient E0 T tau L B s).num :=
  Fraction.nonnegative_add _ _
    (GeneralForceEndpoint.weightedCoefficient_nonnegative E0 T tau L B s hE hT ht hL hB)
    (Fraction.nonnegative_mul _ _ hT (speedCap_nonnegative T tau B s hT ht hB))

-- Modern dependency score: 39/177 (M=39, H=138; transitive project theorems/axioms).
theorem adjacent_weighted_tail (b : Nat → Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    Fraction.le (TimeCalibration.distance tau (prefixState b o E0 T s hE (j+1))
      (prefixState b o E0 T s hE j))
      (GeometricTail.tailCap (weightedCoefficient E0 T tau L B s) (j+1)) := by
  have href := GeneralForceEndpoint.paired_weighted_tail o E0 T tau L B s hE d.toConditions
    j (ticks b j) (ticks_le_blocks b j)
  have hop := count_step_bound o E0 T tau L B s hE d (j+1) (2*ticks b j) (by
    have hn := ticks_lt_blocks b j
    rw [blocks_succ]
    omega)
  have he : Fraction.equiv (Fraction.mul (duration T (j+1)) (speedCap T tau B s))
      (GeometricTail.tailCap (Fraction.mul T (speedCap T tau B s)) (j+1)) := by
    simp only [duration,GeometricTail.tailCap,Fraction.equiv,Fraction.mul]
    ac_nf
  rw [prefix_next]
  by_cases hb : b j
  · rw [ite_eq_left hb]
    have ht := TimeCalibration.distance_triangle tau d.calibration_positive
      (countState o E0 T s hE (j+1) (2*ticks b j+1))
      (countState o E0 T s hE (j+1) (2*ticks b j)) (prefixState b o E0 T s hE j)
    exact Fraction.le_equiv_right
      (Fraction.magnitudes.le_trans ht
        (Fraction.add_le_add (Fraction.le_equiv_right hop he) href))
      (Fraction.equiv_trans (Fraction.add_comm _ _) (GeometricTail.tail_add _ _ (j+1)))
  · rw [ite_eq_right hb]
    have hnon : 0 ≤ (GeometricTail.tailCap (Fraction.mul T (speedCap T tau B s)) (j+1)).num :=
      Fraction.nonnegative_mul _ _ d.time_nonnegative
        (speedCap_nonnegative T tau B s d.time_nonnegative d.calibration_positive d.bound_nonnegative)
    exact Fraction.le_equiv_right
      (Fraction.magnitudes.le_trans href (Fraction.le_add_nonnegative _ _ hnon))
      (GeometricTail.tail_add _ _ (j+1))

noncomputable def coefficient (E0 T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) (TimeCalibration.inverse tau ht))
    (weightedCoefficient E0 T tau L B s)

-- Modern dependency score: 4/8 (M=4, H=4; transitive project theorems/axioms).
theorem coefficient_nonnegative (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num)
    (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (coefficient E0 T tau L B s ht).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos))
    (weightedCoefficient_nonnegative E0 T tau L B s hE hT ht hL hB)

-- Modern dependency score: 40/179 (M=40, H=139; transitive project theorems/axioms).
theorem adjacent_tail (b : Nat → Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    Fraction.le (FiniteEstimates.stateDistance (prefixState b o E0 T s hE (j+1))
      (prefixState b o E0 T s hE j))
      (GeometricTail.tailCap (coefficient E0 T tau L B s d.calibration_positive) (j+1)) := by
  have hC : 0 ≤ (Fraction.add (Fraction.ofInt 1)
      (TimeCalibration.inverse tau d.calibration_positive)).num :=
    Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos)
  have hb := Fraction.magnitudes.le_trans
    (TimeCalibration.uncalibrated_le_distance tau d.calibration_positive _ _)
    (Fraction.mul_le_mul_nonnegative_left
      (adjacent_weighted_tail b o E0 T tau L B s hE d j) _ hC)
  apply Fraction.le_equiv_right hb
  simp only [coefficient,GeometricTail.tailCap,Fraction.equiv,Fraction.mul]
  ac_nf

noncomputable def prefixName (b : Nat → Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE) :
    EndpointCauchyName where
  approx := prefixState b o E0 T s hE
  cauchy := by
    intro eps heps
    let A := coefficient E0 T tau L B s d.calibration_positive
    have hA := coefficient_nonnegative E0 T tau L B s hE d.time_nonnegative
      d.calibration_positive d.lipschitz.1 d.bound_nonnegative
    refine ⟨GeometricTail.modulus A eps,?_⟩
    intro m n hm hn
    exact Fraction.magnitudes.lt_of_le_lt
      (GeometricTail.two_sided _ A hA (adjacent_tail b o E0 T tau L B s hE d) _ m n hm hn)
      (GeometricTail.doubleTail_lt_tolerance A eps hA heps)

-- Modern dependency score: 1/8 (M=1, H=7; transitive project theorems/axioms).
theorem zero_time_prefix (b : Nat → Bool) (o : CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (hT : T.num = 0) (j : Nat) :
    stateEquiv (prefixState b o E0 T s hE j) s :=
  BoundedIteration.zero_duration_run (field o E0 hE j) (duration T j) hT s (ticks b j)

end NewtonLimitDynamics.Polygon.GeneralForcePrefix
