import ModernLib.Polygon.GeneralForceTime
import BarrowLib.Polygon.KinematicEstimates
import ModernLib.Foundation.Polygon.DyadicNodes

/-! Position secants of the actual constructed central-force map converge
to its constructed velocity along the bracketing dyadic cells. The finite
remainder is derived and transferred through Cauchy values. This does not
assert an unrestricted derivative or identify acceleration with force. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceSecants
open NewtonLimitDynamics
open TimeSubdivision PointBounds ForceClasses HarmonicDyadic HarmonicBinaryPrefix
open CauchyValues BinaryTime PositionValues SecantValues DyadicNodes HarmonicTimeRealization
open GeneralForceEndpoint GeneralForcePrefix GeneralForceTime

noncomputable def nodeName (o : CentralOracle) (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m k : Nat) :
    EndpointCauchyName :=
  shiftedName (if k=blocks m then endpointName o E0 T tau L B s hE d.toConditions
    else prefixName (finiteAddress m k) o E0 T tau L B s hE d) m

theorem node_approx (o : CentralOracle) (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (m k : Nat) (hk : k≤blocks m) (j : Nat) :
    (nodeName o E0 T tau L B s hE d m k).approx j =
      GeneralForcePrefix.countState o E0 T s hE (m+j) (k*blocks j) := by
  by_cases he : k=blocks m
  · rw [nodeName,if_pos he]
    change GeneralForcePrefix.countState o E0 T s hE (m+j) (blocks (m+j)) = _
    rw [blocks_add,he]
  · rw [nodeName,if_neg he]
    change GeneralForcePrefix.countState o E0 T s hE (m+j)
      (ticks (finiteAddress m k) (m+j)) = _
    rw [finiteAddress_later_ticks m k j (by omega)]

theorem node_value (o : CentralOracle) (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m k : Nat) :
    realize (nodeName o E0 T tau L B s hE d m k) =
      GeneralForceTime.gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k) := by
  by_cases he : k=blocks m
  · rw [nodeName,if_pos he,shiftedValue,nodeTime,if_pos he]
    exact (GeneralForceTime.right_endpoint_value o E0 T tau L B s hE d).symm
  · rw [nodeName,if_neg he,shiftedValue,nodeTime,if_neg he]
    rfl

theorem node_region (o : CentralOracle) (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (m k j : Nat) : o.region ((nodeName o E0 T tau L B s hE d m k).approx j).1 := by
  by_cases he : k=blocks m
  · simp only [nodeName,if_pos he,shiftedName]
    exact d.toConditions.run_region (m+j) (duration T (m+j)) d.time_nonnegative
      (blocks (m+j)) (Fraction.le_of_equiv (blocks_duration T (m+j)))
  · simp only [nodeName,if_neg he,shiftedName]
    exact prefix_region (finiteAddress m k) o E0 T tau L B s hE d (m+j)

theorem node_admissible (o : CentralOracle) (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m k : Nat) :
    SampledValues.Admissible (fun q => o.region q.1) (realize (nodeName o E0 T tau L B s hE d m k)) :=
  SampledValues.admissible_realize _ _ (node_region o E0 T tau L B s hE d m k)

/-- A secant of completed curve values, divided by the actual coarse cell time. -/
noncomputable def cellSecant (o : CentralOracle) (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (hT : 0 < T.num) (m k : Nat) : Value :=
  secantValue (TimeCalibration.inverse (duration T m) hT)
    (GeneralForceTime.gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m (k+1)))
    (GeneralForceTime.gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))

/-- Actual finite drift remainders pass to the secant of the completed curve. -/
theorem cell_secant_bound (o : CentralOracle) (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (hT : 0 < T.num) (m k : Nat) (hk : k+1≤blocks m) :
    Within (cellSecant o E0 T tau L B s hE d hT m k)
      (velocityValue (GeneralForceTime.gammaValue o E0 T tau L B s hE d
        (nodeTime T d.time_nonnegative m k))) (Fraction.mul (duration T m) B) := by
  rw [cellSecant,← node_value o E0 T tau L B s hE d m (k+1),
    ← node_value o E0 T tau L B s hE d m k]
  change NameBound
    (secantName (TimeCalibration.inverse (duration T m) hT)
      (nodeName o E0 T tau L B s hE d m (k+1)) (nodeName o E0 T tau L B s hE d m k))
    (mapName velocityState velocity_nonexpansive (nodeName o E0 T tau L B s hE d m k)) _
  apply nameBound_of_eventual_le _ _ _ 0
  intro j _
  change Fraction.le
    (distance (secantState (TimeCalibration.inverse (duration T m) hT)
      ((nodeName o E0 T tau L B s hE d m (k+1)).approx j)
      ((nodeName o E0 T tau L B s hE d m k).approx j))
      (velocityState ((nodeName o E0 T tau L B s hE d m k).approx j))) _
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
  have hb := BoundedIteration.boundedSamples_restart a h s B (blocks (m+j)) n (blocks j)
    hn (d.actual_samples (m+j))
  have hp : 0 < (blocks j : Int) := Int.ofNat_pos.mpr (by unfold blocks; exact Nat.pow_pos (by decide))
  have ht : 0 < (BoundedIteration.time h (blocks j)).num := Int.mul_pos hp hT
  have hr := KinematicEstimates.position_secant_equivalent_time a h q B (duration T m)
    (Int.le_of_lt hT) d.bound_nonnegative (blocks j) ht hT
    (Fraction.equiv_symm (grid_time T m j)) hb
  have he : n+blocks j=(k+1)*blocks j := by simp only [n,Nat.add_mul,Nat.one_mul]
  change Fraction.le
    (FiniteEstimates.pointDistance
      (pointScale (TimeCalibration.inverse (duration T m) hT)
        (pointSub (BoundedIteration.run a h (BoundedIteration.run a h s n) (blocks j)).1
          (BoundedIteration.run a h s n).1)) (BoundedIteration.run a h s n).2) _ at hr
  rw [← BoundedIteration.run_add,he] at hr
  exact Fraction.le_equiv_left (pointState_distance _ _) hr

noncomputable def rateCoefficient (T tau B : Fraction) (s : Point × Point) (ht : 0 < tau.num) : Fraction :=
  Fraction.add B (GeneralForceTime.stateTimeFactor T tau B s ht)

theorem rateCoefficient_nonnegative (T tau B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hB : 0 ≤ B.num) :
    0 ≤ (rateCoefficient T tau B s ht).num :=
  Fraction.nonnegative_add _ _ hB (GeneralForceTime.stateTimeFactor_nonnegative T tau B s hT ht hB)

/-- This secant uses both actual completed cell endpoints, including the right edge. -/
theorem bracketing_secant_bound (b : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num) (m : Nat) :
    Within (cellSecant o E0 T tau L B s hE d hT m (ticks b m))
      (velocityValue (GeneralForceTime.gammaValue o E0 T tau L B s hE d (Quotient.mk _ b)))
      (Fraction.mul (duration T m) (rateCoefficient T tau B s d.calibration_positive)) := by
  have hs := cell_secant_bound o E0 T tau L B s hE d hT m (ticks b m) (by
    have hn := ticks_lt_blocks b m
    omega)
  have hv := velocityValue_within _ _ _ (GeneralForceTime.gamma_within o E0 T tau L B s hE d
    (nodeTime T d.time_nonnegative m (ticks b m)) (Quotient.mk _ b) (duration T m)
    (truncation_time_within b T d.time_nonnegative m))
  have hb := within_triangle _ _ _ _ _ hs hv
  exact within_mono _ _ _ _ (Fraction.le_of_equiv (Fraction.equiv_symm (Fraction.mul_add _ _ _))) hb

/-- Constructed velocity is the limit of the completed bracketing position secants. -/
theorem dyadic_velocity_uniform_identification (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ b : Nat → Bool,
      Within (cellSecant o E0 T tau L B s hE d hT m (ticks b m))
        (velocityValue (GeneralForceTime.gammaValue o E0 T tau L B s hE d (Quotient.mk _ b))) eps := by
  let C := rateCoefficient T tau B s d.calibration_positive
  have hC := rateCoefficient_nonnegative T tau B s d.time_nonnegative d.calibration_positive d.bound_nonnegative
  have hTC : 0 ≤ (Fraction.mul T C).num := Fraction.nonnegative_mul _ _ d.time_nonnegative hC
  obtain ⟨N,hN⟩ := duration_eventually_small (Fraction.mul T C) eps hTC heps
  refine ⟨N,fun m hm b => ?_⟩
  have he : Fraction.equiv (Fraction.mul (duration T m) C) (duration (Fraction.mul T C) m) := by
    simp only [duration,Fraction.equiv,Fraction.mul]
    ac_nf
  exact within_mono _ _ _ _ (Fraction.le_equiv_left he (Fraction.magnitudes.lt_implies_le (hN m hm)))
    (bracketing_secant_bound b o E0 T tau L B s hE d hT m)

theorem dyadic_velocity_identification (b : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m →
      Within (cellSecant o E0 T tau L B s hE d hT m (ticks b m))
        (velocityValue (GeneralForceTime.gammaValue o E0 T tau L B s hE d (Quotient.mk _ b))) eps := by
  obtain ⟨N,hN⟩ := dyadic_velocity_uniform_identification o E0 T tau L B s hE d hT eps heps
  exact ⟨N,fun m hm => hN m hm b⟩

end NewtonLimitDynamics.Polygon.GeneralForceSecants
