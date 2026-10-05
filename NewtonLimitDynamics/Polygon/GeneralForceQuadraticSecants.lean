import NewtonLimitDynamics.Polygon.GeneralForceAccelerationSecants
import BarrowLib.Polygon.QuadraticSecants

/-! The normalized departure from the constructed tangent over a dyadic cell
converges to the completed force. Finite quadratic remainders and proved
Cauchy-name boundedness remove the actual half-mesh and sampling errors.
No Taylor expansion, derivative or desired second-order equation is supplied. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceQuadraticSecants
open NewtonLimitDynamics
open TimeSubdivision PointBounds ForceClasses HarmonicDyadic HarmonicBinaryPrefix
open CauchyValues BinaryTime PositionValues SecantValues DyadicNodes HarmonicTimeRealization
open GeneralForceEndpoint GeneralForcePrefix GeneralForceTime GeneralForceSecants

noncomputable def cellSecondSecant (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num) (m k : Nat) : Value :=
  QuadraticSecants.secondValue (duration T m) hT
    (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))
    (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m (k+1)))

/-- The actual finite node approximants retain their sample and half-mesh
errors. Both the completed second-order bridge and potential calculations use
this estimate, rather than repeating the restarted-run proof. -/
theorem node_second_sample_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (m k : Nat) (hk : k+1≤blocks m) (j : Nat) :
    Fraction.le
      (FiniteEstimates.pointDistance (QuadraticSecants.secondState (duration T m) hT
        ((nodeName o E0 T tau L B s hE d m k).approx j)
        ((nodeName o E0 T tau L B s hE d m (k+1)).approx j)).1
        (field o E0 hE (m+j) ((nodeName o E0 T tau L B s hE d m k).approx j).1))
      (Fraction.add
        (Fraction.mul (Fraction.ofInt 2) (Fraction.mul L (Fraction.mul (duration T m) (velocityCap T B s))))
        (Fraction.add (Fraction.mul (sampleError o E0 hE (m+j)) (Fraction.ofInt 2))
          (Fraction.mul (duration (Fraction.ofInt 1) j)
            (pointNorm (field o E0 hE (m+j) ((nodeName o E0 T tau L B s hE d m k).approx j).1))))) := by
  rw [node_approx o E0 T tau L B s hE d m k (by omega) j,
    node_approx o E0 T tau L B s hE d m (k+1) hk j]
  let a := field o E0 hE (m+j)
  let h := duration T (m+j)
  let n := k*blocks j
  let q := GeneralForcePrefix.countState o E0 T s hE (m+j) n
  have hn : n+blocks j ≤ blocks (m+j) := by
    rw [blocks_add]
    have hm := Nat.mul_le_mul_right (blocks j) hk
    simpa only [n,Nat.add_mul,Nat.one_mul] using hm
  have hp : 0 < (blocks j : Int) := Int.ofNat_pos.mpr (by unfold blocks; exact Nat.pow_pos (by decide))
  have ht : 0 < (BoundedIteration.time h (blocks j)).num := Int.mul_pos hp hT
  have hv : ∀ i, i<blocks j → Fraction.le
      (pointNorm (BoundedIteration.run a h q i).2) (velocityCap T B s) := by
    intro i hi
    change Fraction.le (pointNorm (BoundedIteration.run a h (BoundedIteration.run a h s n) i).2) _
    rw [← BoundedIteration.run_add]
    exact GeneralForcePrefix.count_velocity o E0 T tau L B s hE d (m+j) (n+i) (by omega)
  have hr := QuadraticSecants.finite_second_equivalent_time a h q L (sampleError o E0 hE (m+j))
    (velocityCap T B s) (duration T m) (Int.le_of_lt hT) d.lipschitz.1
    (sampleError_nonnegative o E0 hE (m+j))
    (velocityCap_nonnegative T B s d.time_nonnegative d.bound_nonnegative)
    (local_contract o E0 T tau L B s hE d.toConditions (m+j)) (blocks j) ht hT
    (Fraction.equiv_symm (grid_time T m j)) hv
  have he : n+blocks j=(k+1)*blocks j := by simp only [n,Nat.add_mul,Nat.one_mul]
  change Fraction.le (FiniteEstimates.pointDistance
    (QuadraticSecants.secondState (duration T m) hT (BoundedIteration.run a h s n)
      (BoundedIteration.run a h (BoundedIteration.run a h s n) (blocks j))).1
    (a (BoundedIteration.run a h s n).1)) _ at hr
  rw [← BoundedIteration.run_add,he] at hr
  have hbias : Fraction.equiv (Fraction.mul h (TimeCalibration.inverse (duration T m) hT))
      (duration (Fraction.ofInt 1) j) := by
    simp only [h,duration,TimeCalibration.inverse,Fraction.equiv,Fraction.mul,Fraction.ofInt,
      FiniteGrowth.denominator_power_add]
    ac_nf
  apply Fraction.le_equiv_right hr
  apply Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _)
    (Fraction.mul_equiv hbias (Fraction.equiv_refl _)))
  simp only [AccelerationEstimates.source,Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
  ac_nf

theorem cell_second_secant_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (m k : Nat) (hk : k+1≤blocks m) :
    Within (cellSecondSecant o E0 T tau L B s hE d hT m k)
      (CompletedForce.forceValue o E0 L hE d.lipschitz d.global_region
        (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k)))
      (Fraction.mul (Fraction.ofInt 2) (Fraction.mul L (Fraction.mul (duration T m) (velocityCap T B s)))) := by
  rw [cellSecondSecant,QuadraticSecants.secondValue,
    ← node_value o E0 T tau L B s hE d m k,← node_value o E0 T tau L B s hE d m (k+1)]
  let f := CompletedForce.family o E0 L hE d.lipschitz d.global_region
  change Within (realize (secantName (Fraction.mul (Fraction.ofInt 2) (TimeCalibration.inverse (duration T m) hT))
    (secantName (TimeCalibration.inverse (duration T m) hT)
      (nodeName o E0 T tau L B s hE d m (k+1)) (nodeName o E0 T tau L B s hE d m k))
    (mapName velocityState velocity_nonexpansive (nodeName o E0 T tau L B s hE d m k))))
    (SampledValues.sampledValue f (realize (nodeName o E0 T tau L B s hE d m k))) _
  rw [← SampledValues.sampledValue_offset f _ m]
  let g := SampledValues.sampledName (SampledValues.offsetFamily f m) (nodeName o E0 T tau L B s hE d m k)
  change NameBound _ g _
  apply SampledValues.nameBound_of_vanishing_error _ _ _ (fun j =>
    Fraction.add (Fraction.mul (sampleError o E0 hE (m+j)) (Fraction.ofInt 2))
      (Fraction.mul (duration (Fraction.ofInt 1) j) (pointNorm (g.approx j).1)))
  · intro eps heps
    let delta := factorDelta (Fraction.ofInt 2) eps.half (by decide)
    have hd : 0 < delta.num := factorDelta_positive _ _ _ heps
    obtain ⟨N,hN⟩ := CompletedForce.sampleError_vanishes o E0 hE delta hd
    obtain ⟨M,hM⟩ := mesh_position_product_vanishes g eps.half heps
    refine ⟨max N M,fun j hj => ?_⟩
    have h1 := factor_control (Fraction.ofInt 2) eps.half (sampleError o E0 hE (m+j))
      (by decide) (sampleError_nonnegative o E0 hE (m+j)) (hN (m+j) (by omega))
    exact CauchyValues.lt_equiv_right (Fraction.add_lt_add h1 (hM j (by omega))) (Fraction.half_add_self eps)
  · intro j
    change Fraction.le
      (distance (QuadraticSecants.secondState (duration T m) hT
        ((nodeName o E0 T tau L B s hE d m k).approx j)
        ((nodeName o E0 T tau L B s hE d m (k+1)).approx j))
        (accelerationState (field o E0 hE (m+j) ((nodeName o E0 T tau L B s hE d m k).approx j).1)))
      (Fraction.add _ (Fraction.add (Fraction.mul (sampleError o E0 hE (m+j)) (Fraction.ofInt 2))
        (Fraction.mul (duration (Fraction.ofInt 1) j)
          (pointNorm (field o E0 hE (m+j) ((nodeName o E0 T tau L B s hE d m k).approx j).1)))))
    exact Fraction.le_equiv_left (pointState_distance _ _)
      (node_second_sample_bound o E0 T tau L B s hE d hT m k hk j)

noncomputable def secondCoefficient (T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) : Fraction :=
  Fraction.mul L (Fraction.add (Fraction.mul (Fraction.ofInt 2) (velocityCap T B s))
    (stateTimeFactor T tau B s ht))

theorem secondCoefficient_nonnegative (T tau L B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (secondCoefficient T tau L B s ht).num :=
  Fraction.nonnegative_mul _ _ hL (Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ (by decide) (velocityCap_nonnegative T B s hT hB))
    (stateTimeFactor_nonnegative T tau B s hT ht hB))

theorem bracketing_second_secant_bound (b : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num) (m : Nat) :
    Within (cellSecondSecant o E0 T tau L B s hE d hT m (ticks b m))
      (CompletedForce.forceValue o E0 L hE d.lipschitz d.global_region
        (gammaValue o E0 T tau L B s hE d (Quotient.mk _ b)))
      (Fraction.mul (duration T m) (secondCoefficient T tau L B s d.calibration_positive)) := by
  have hs := cell_second_secant_bound o E0 T tau L B s hE d hT m (ticks b m)
    (by have hn := ticks_lt_blocks b m; omega)
  have hf := CompletedForce.forceValue_within o E0 L hE d.lipschitz d.global_region _ _ _
    (gamma_within o E0 T tau L B s hE d
      (nodeTime T d.time_nonnegative m (ticks b m)) (Quotient.mk _ b) (duration T m)
      (truncation_time_within b T d.time_nonnegative m))
  have hb := within_triangle _ _ _ _ _ hs hf
  apply within_mono _ _ _ _ ?_ hb
  apply Fraction.le_of_equiv
  simp only [secondCoefficient,Fraction.equiv,Fraction.mul,Fraction.add,Int.add_mul,Int.mul_add]
  ac_nf

/-- The half-coefficient position departure is derived on the actual
completed curve at every bracketing dyadic cell, including the final boundary. -/
theorem dyadic_second_uniform_identification (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ b : Nat → Bool,
      Within (cellSecondSecant o E0 T tau L B s hE d hT m (ticks b m))
        (CompletedForce.forceValue o E0 L hE d.lipschitz d.global_region
          (gammaValue o E0 T tau L B s hE d (Quotient.mk _ b))) eps := by
  let C := secondCoefficient T tau L B s d.calibration_positive
  have hC := secondCoefficient_nonnegative T tau L B s d.time_nonnegative
    d.calibration_positive d.lipschitz.1 d.bound_nonnegative
  obtain ⟨N,hN⟩ := duration_eventually_small (Fraction.mul T C) eps
    (Fraction.nonnegative_mul _ _ d.time_nonnegative hC) heps
  have he : ∀ m, Fraction.equiv (Fraction.mul (duration T m) C) (duration (Fraction.mul T C) m) := by
    intro m
    simp only [duration,Fraction.equiv,Fraction.mul]
    ac_nf
  exact ⟨N,fun m hm b => within_mono _ _ _ _
    (Fraction.le_equiv_left (he m) (Fraction.magnitudes.lt_implies_le (hN m hm)))
    (bracketing_second_secant_bound b o E0 T tau L B s hE d hT m)⟩

end NewtonLimitDynamics.Polygon.GeneralForceQuadraticSecants
