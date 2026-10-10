import ModernLib.Polygon.GeneralForceSecants
import ModernLib.Polygon.CompletedForce
import BarrowLib.Polygon.AccelerationEstimates

-- Retain the 4.19 elaborator's unfolding behavior during the toolchain migration.
set_option backward.isDefEq.respectTransparency false

/-! Completed dyadic velocity secants converge to the completed force at the
constructed positions. Actual finite velocity remainders and force sampling
error derive the estimate; no acceleration equation is a premise. The result
is a bracketing dyadic secant criterion, not unrestricted differentiation. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceAccelerationSecants
open NewtonLimitDynamics
open TimeSubdivision PointBounds ForceClasses HarmonicDyadic HarmonicBinaryPrefix
open CauchyValues BinaryTime PositionValues SecantValues DyadicNodes HarmonicTimeRealization
open GeneralForceEndpoint GeneralForcePrefix GeneralForceTime GeneralForceSecants

/-- Replace a curve input by its certified node representative as a whole
force value, so dependent region certificates are transported together. -/
-- Modern dependency score: 90/260 (M=90, H=170; transitive project theorems/axioms).
theorem node_force_value (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m k : Nat) :
    CompletedForce.forceValue o E0 L hE d.lipschitz
      (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))
      (gamma_admissible o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k)) =
    CompletedForce.forceValue o E0 L hE d.lipschitz
      (realize (nodeName o E0 T tau L B s hE d m k))
      (node_admissible o E0 T tau L B s hE d m k) :=
  SampledValues.sampledValue_congr (CompletedForce.family o E0 L hE d.lipschitz) _ _
    (gamma_admissible o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))
    (node_admissible o E0 T tau L B s hE d m k)
    (node_value o E0 T tau L B s hE d m k).symm

noncomputable def cellAccelerationSecant (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num) (m k : Nat) : Value :=
  secantValue (TimeCalibration.inverse (duration T m) hT)
    (velocityValue (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m (k+1))))
    (velocityValue (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k)))

-- Modern dependency score: 121/310 (M=121, H=189; transitive project theorems/axioms).
theorem cell_acceleration_secant_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (m k : Nat) (hk : k+1≤blocks m) :
    Within (cellAccelerationSecant o E0 T tau L B s hE d hT m k)
      (CompletedForce.forceValue o E0 L hE d.lipschitz (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))
        (gamma_admissible o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k)))
      (Fraction.mul L (Fraction.mul (duration T m) (velocityCap T B s))) := by
  rw [node_force_value o E0 T tau L B s hE d m k,cellAccelerationSecant,← node_value o E0 T tau L B s hE d m (k+1),
    ← node_value o E0 T tau L B s hE d m k]
  let f := CompletedForce.family o E0 L hE d.lipschitz
  change Within
    (realize (secantName (TimeCalibration.inverse (duration T m) hT)
      (mapName velocityState velocity_nonexpansive (nodeName o E0 T tau L B s hE d m (k+1)))
      (mapName velocityState velocity_nonexpansive (nodeName o E0 T tau L B s hE d m k))))
    (SampledValues.sampledValue f (realize (nodeName o E0 T tau L B s hE d m k))
      (node_admissible o E0 T tau L B s hE d m k)) _
  rw [← SampledValues.sampledValue_offset f _ _ m,
    SampledValues.sampledValue_realize (SampledValues.offsetFamily f m)
      (nodeName o E0 T tau L B s hE d m k) (node_region o E0 T tau L B s hE d m k)]
  change NameBound _ _ _
  apply SampledValues.nameBound_of_vanishing_error _ _ _ (fun j => sampleError o E0 hE (m+j))
  · intro eps heps
    obtain ⟨N,hN⟩ := CompletedForce.sampleError_vanishes o E0 hE eps heps
    exact ⟨N,fun j hj => hN (m+j) (by omega)⟩
  · intro j
    change Fraction.le
      (distance (secantState (TimeCalibration.inverse (duration T m) hT)
        (velocityState ((nodeName o E0 T tau L B s hE d m (k+1)).approx j))
        (velocityState ((nodeName o E0 T tau L B s hE d m k).approx j)))
        (accelerationState (field o E0 hE (m+j)
          ((nodeName o E0 T tau L B s hE d m k).approx j).1))) _
    rw [node_approx o E0 T tau L B s hE d m (k+1) hk j,
      node_approx o E0 T tau L B s hE d m k (by omega) j]
    let a := field o E0 hE (m+j)
    let h := duration T (m+j)
    let n := k*blocks j
    let q := GeneralForcePrefix.countState o E0 T s hE (m+j) n
    have hn : n+blocks j ≤ blocks (m+j) := by
      rw [blocks_add]
      have hm := Nat.mul_le_mul_right (blocks j) hk
      simpa only [n,Nat.add_mul,Nat.one_mul] using hm
    have hp : 0 < (blocks j : Int) := Int.natCast_pos.mpr (by unfold blocks; exact Nat.pow_pos (by decide))
    have ht : 0 < (BoundedIteration.time h (blocks j)).num := Int.mul_pos hp hT
    have hv : ∀ i, i<blocks j → Fraction.le
        (pointNorm (BoundedIteration.run a h q i).2) (velocityCap T B s) := by
      intro i hi
      change Fraction.le
        (pointNorm (BoundedIteration.run a h (BoundedIteration.run a h s n) i).2) _
      rw [← BoundedIteration.run_add]
      exact GeneralForcePrefix.count_velocity o E0 T tau L B s hE d (m+j) (n+i) (by omega)
    have hr := AccelerationEstimates.acceleration_secant_equivalent_time_at a h q L
      (sampleError o E0 hE (m+j)) (velocityCap T B s) (duration T m)
      (Int.le_of_lt hT) d.lipschitz.1
      (velocityCap_nonnegative T B s d.time_nonnegative d.bound_nonnegative)
      (blocks j) ht
      (fun i hi => restarted_comparison o E0 T tau L B s hE d (m+j) n (blocks j) hn i hi) hT (Fraction.equiv_symm (grid_time T m j)) hv
    have he : n+blocks j=(k+1)*blocks j := by simp only [n,Nat.add_mul,Nat.one_mul]
    change Fraction.le (FiniteEstimates.pointDistance
      (pointScale (TimeCalibration.inverse (duration T m) hT)
        (pointSub (BoundedIteration.run a h (BoundedIteration.run a h s n) (blocks j)).2
          (BoundedIteration.run a h s n).2)) (a (BoundedIteration.run a h s n).1)) _ at hr
    rw [← BoundedIteration.run_add,he] at hr
    exact Fraction.le_equiv_left (pointState_distance _ _) hr

noncomputable def accelerationCoefficient (T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) : Fraction :=
  Fraction.mul L (Fraction.add (velocityCap T B s) (stateTimeFactor T tau B s ht))

-- Modern dependency score: 3/7 (M=3, H=4; transitive project theorems/axioms).
theorem accelerationCoefficient_nonnegative (T tau L B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (accelerationCoefficient T tau L B s ht).num :=
  Fraction.nonnegative_mul _ _ hL (Fraction.nonnegative_add _ _
    (velocityCap_nonnegative T B s hT hB) (stateTimeFactor_nonnegative T tau B s hT ht hB))

-- Modern dependency score: 143/338 (M=143, H=195; transitive project theorems/axioms).
theorem bracketing_acceleration_secant_bound (b : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num) (m : Nat) :
    Within (cellAccelerationSecant o E0 T tau L B s hE d hT m (ticks b m))
      (CompletedForce.forceValue o E0 L hE d.lipschitz (gammaValue o E0 T tau L B s hE d (Quotient.mk _ b))
        (gamma_admissible o E0 T tau L B s hE d (Quotient.mk _ b)))
      (Fraction.mul (duration T m) (accelerationCoefficient T tau L B s d.calibration_positive)) := by
  have hs := cell_acceleration_secant_bound o E0 T tau L B s hE d hT m (ticks b m)
    (by have hn := ticks_lt_blocks b m; omega)
  have hf := CompletedForce.forceValue_within o E0 L hE d.lipschitz _ _
    (gamma_admissible o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m (ticks b m)))
    (gamma_admissible o E0 T tau L B s hE d (Quotient.mk _ b)) _
    (gamma_within o E0 T tau L B s hE d
      (nodeTime T d.time_nonnegative m (ticks b m)) (Quotient.mk _ b) (duration T m)
      (truncation_time_within b T d.time_nonnegative m))
  have hb := within_triangle _ _ _ _ _ hs hf
  apply within_mono _ _ _ _ ?_ hb
  apply Fraction.le_of_equiv
  simp only [accelerationCoefficient,Fraction.equiv,Fraction.mul,Fraction.add,Int.add_mul,Int.mul_add]
  ac_nf

/-- The force at the constructed position is the uniform limit of completed
bracketing dyadic velocity secants. No acceleration is supplied as data. -/
-- Modern dependency score: 145/340 (M=145, H=195; transitive project theorems/axioms).
theorem dyadic_acceleration_uniform_identification (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ b : Nat → Bool,
      Within (cellAccelerationSecant o E0 T tau L B s hE d hT m (ticks b m))
        (CompletedForce.forceValue o E0 L hE d.lipschitz (gammaValue o E0 T tau L B s hE d (Quotient.mk _ b))
        (gamma_admissible o E0 T tau L B s hE d (Quotient.mk _ b))) eps := by
  let C := accelerationCoefficient T tau L B s d.calibration_positive
  have hC := accelerationCoefficient_nonnegative T tau L B s d.time_nonnegative
    d.calibration_positive d.lipschitz.1 d.bound_nonnegative
  obtain ⟨N,hN⟩ := duration_eventually_small (Fraction.mul T C) eps
    (Fraction.nonnegative_mul _ _ d.time_nonnegative hC) heps
  refine ⟨N,fun m hm b => ?_⟩
  have he : Fraction.equiv (Fraction.mul (duration T m) C) (duration (Fraction.mul T C) m) := by
    simp only [duration,Fraction.equiv,Fraction.mul]
    ac_nf
  exact within_mono _ _ _ _
    (Fraction.le_equiv_left he (Fraction.magnitudes.lt_implies_le (hN m hm)))
    (bracketing_acceleration_secant_bound b o E0 T tau L B s hE d hT m)

end NewtonLimitDynamics.Polygon.GeneralForceAccelerationSecants
