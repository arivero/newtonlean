import ModernLib.Polygon.GeneralForcePrefix
import ModernLib.Foundation.Polygon.BinaryEndpoints
import BarrowLib.Polygon.FiniteSequenceGap
import ModernLib.Foundation.Polygon.PositionValues
import ModernLib.Foundation.Polygon.TailValues
import ModernLib.Foundation.Polygon.SampledValues
import ModernLib.Foundation.Polygon.CompletionGeometry

/-! A local general sampled central-force time map, constructed from actual
prefixes. Same-grid drift/kick bounds prove representative invariance before
the time quotient is lifted. This is a binary-time domain, not a supplied
real trajectory or a derivative/ODE identification. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceTime
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix HarmonicTimeComparison
open GeneralForceEndpoint GeneralForcePrefix CauchyValues BinaryTime
open HarmonicTimeRealization

noncomputable def stateTimeFactor (T tau B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) (TimeCalibration.inverse tau ht))
    (speedCap T tau B s)

-- Modern dependency score: 2/6 (M=2, H=4; transitive project theorems/axioms).
theorem stateTimeFactor_nonnegative (T tau B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hB : 0 ≤ B.num) :
    0 ≤ (stateTimeFactor T tau B s ht).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos))
    (speedCap_nonnegative T tau B s hT ht hB)

-- Modern dependency score: 18/82 (M=18, H=64; transitive project theorems/axioms).
theorem count_gap (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (j n k : Nat) (hnk : n+k ≤ blocks j) :
    Fraction.le (TimeCalibration.distance tau (countState o E0 T s hE j (n+k))
      (countState o E0 T s hE j n))
      (Fraction.mul (Fraction.ofInt (k : Int))
        (Fraction.mul (duration T j) (speedCap T tau B s))) :=
  FiniteSequenceGap.finite_gap (TimeCalibration.distance tau) (TimeCalibration.distance_self_zero tau)
    (TimeCalibration.distance_triangle tau d.calibration_positive)
    (countState o E0 T s hE j) (blocks j) (Fraction.mul (duration T j) (speedCap T tau B s))
    (fun i hi => count_step_bound o E0 T tau L B s hE d j i hi) n k hnk

-- Modern dependency score: 19/86 (M=19, H=67; transitive project theorems/axioms).
theorem count_ordered_bound (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (j n k : Nat) (hnk : n+k ≤ blocks j) :
    Fraction.le (TimeCalibration.distance tau (countState o E0 T s hE j (n+k))
      (countState o E0 T s hE j n))
      (Fraction.mul (durationDifference (countTime T j n) (countTime T j (n+k))).abs
        (speedCap T tau B s)) := by
  apply Fraction.le_equiv_right (count_gap o E0 T tau L B s hE d j n k hnk)
  exact Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))
    (Fraction.mul_equiv (Fraction.equiv_symm (countTime_abs_difference T j n k d.time_nonnegative))
      (Fraction.equiv_refl _))

-- Modern dependency score: 20/91 (M=20, H=71; transitive project theorems/axioms).
theorem count_same_grid_bound (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (j m n : Nat) (hm : m ≤ blocks j) (hn : n ≤ blocks j) :
    Fraction.le (TimeCalibration.distance tau (countState o E0 T s hE j m)
      (countState o E0 T s hE j n))
      (Fraction.mul (durationDifference (countTime T j n) (countTime T j m)).abs
        (speedCap T tau B s)) := by
  rcases Nat.le_total n m with hnm | hmn
  · have he : n+(m-n)=m := by omega
    have hb := count_ordered_bound o E0 T tau L B s hE d j n (m-n) (by omega)
    simpa only [he] using hb
  · have he : m+(n-m)=n := by omega
    have hb := count_ordered_bound o E0 T tau L B s hE d j m (n-m) (by omega)
    rw [he] at hb
    exact Fraction.le_equiv_right
      (Fraction.le_equiv_left (TimeCalibration.distance_symm tau _ _) hb)
      (Fraction.mul_equiv (durationDifference_abs_symm _ _) (Fraction.equiv_refl _))

/-- Actual same-family prefixes are Lipschitz in their actual grid times. -/
-- Modern dependency score: 23/99 (M=23, H=76; transitive project theorems/axioms).
theorem prefix_time_bound (b c : Nat → Bool) (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (j : Nat) :
    Fraction.le (distance (prefixState b o E0 T s hE j) (prefixState c o E0 T s hE j))
      (Fraction.mul (distance (timeState b T j) (timeState c T j))
        (stateTimeFactor T tau B s d.calibration_positive)) := by
  let C := Fraction.add (Fraction.ofInt 1) (TimeCalibration.inverse tau d.calibration_positive)
  have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos)
  have hb := Fraction.magnitudes.le_trans (TimeCalibration.uncalibrated_le_distance tau d.calibration_positive _ _)
    (Fraction.mul_le_mul_nonnegative_left
      (count_same_grid_bound o E0 T tau L B s hE d j (ticks b j) (ticks c j)
        (ticks_le_blocks b j) (ticks_le_blocks c j)) C hC)
  apply Fraction.le_equiv_right hb
  exact Fraction.equiv_trans (by
    simp only [C,stateTimeFactor,countTime,timeApprox,Fraction.equiv,Fraction.mul]
    ac_nf) (Fraction.mul_equiv
      (Fraction.equiv_symm (timeState_distance b c T j)) (Fraction.equiv_refl _))

-- Modern dependency score: 56/215 (M=56, H=159; transitive project theorems/axioms).
theorem address_state_equiv (b c : Nat → Bool) (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (hbc : AddressEquiv T d.time_nonnegative b c) :
    NameEquiv (prefixName b o E0 T tau L B s hE d) (prefixName c o E0 T tau L B s hE d) := by
  intro eps heps
  let C := stateTimeFactor T tau B s d.calibration_positive
  have hC := stateTimeFactor_nonnegative T tau B s d.time_nonnegative d.calibration_positive d.bound_nonnegative
  obtain ⟨N,hN⟩ := hbc (Fraction.ofRat (factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC))) ((by
      apply (Fraction.positive_iff_toRat _).mpr
      change 0 < (Fraction.ofRat _).toRat
      rw [Fraction.toRat_ofRat]
      have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
      have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
      (try dsimp only at hcoef hepsRat ⊢)
      grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
  refine ⟨N,fun j hj => ?_⟩
  exact Fraction.magnitudes.lt_of_le_lt (prefix_time_bound b c o E0 T tau L B s hE d j)
    ((show Fraction.lt (Fraction.mul ((distance (timeState b T j) (timeState c T j))) (C)) (eps) from by
        apply (Fraction.lt_iff_toRat _ _).mpr
        rw [Fraction.toRat_mul]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hdist := ((Fraction.nonnegative_iff_toRat (distance (timeState b T j) (timeState c T j))).mp (stateNorm_nonnegative _))
        have hstrict := (Fraction.lt_iff_toRat _ _).mp (hN j hj)
        change (distance (timeState b T j) (timeState c T j)).toRat < (Fraction.ofRat _).toRat at hstrict
        rw [Fraction.toRat_ofRat] at hstrict
        (try dsimp only at hcoef hdist hstrict ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff]))

noncomputable def gammaValue (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    BinaryTime T d.time_nonnegative → Value :=
  Quotient.lift (fun b => realize (prefixName b o E0 T tau L B s hE d))
    (fun b c hbc => Quotient.sound (address_state_equiv b c o E0 T tau L B s hE d hbc))

/-- The inner and outer radii hold at every actual prefix vertex. -/
-- Modern dependency score: 14/67 (M=14, H=53; transitive project theorems/axioms).
theorem prefix_band (b : Nat → Bool) (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (j : Nat) :
    RegionConfinement.Band d.inner_radius d.outer_radius (prefixState b o E0 T s hE j).1 :=
  d.toConditions.run_band j (duration T j) d.time_nonnegative (ticks b j)
    (count_time_le T d.time_nonnegative j (ticks b j) (ticks_le_blocks b j))

/-- Actual prefix membership is derived from the central confinement frame. -/
-- Modern dependency score: 15/68 (M=15, H=53; transitive project theorems/axioms).
theorem prefix_region (b : Nat → Bool) (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (j : Nat) :
    o.region (prefixState b o E0 T s hE j).1 :=
  d.frame.contains_band _ (prefix_band b o E0 T tau L B s hE d j)

/-- The constructed curve has a regional representative at every time. -/
-- Modern dependency score: 70/233 (M=70, H=163; transitive project theorems/axioms).
theorem gamma_admissible (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (x : BinaryTime T d.time_nonnegative) :
    SampledValues.Admissible (fun q => o.region q.1) (gammaValue o E0 T tau L B s hE d x) := by
  induction x using Quotient.inductionOn with
  | _ b => exact ⟨prefixName b o E0 T tau L B s hE d,rfl,
      prefix_region b o E0 T tau L B s hE d⟩

/-- Every constructed curve position lies in the closed coordinate band.
The lower radius is stated by exclusion of smaller closed balls, without a
new completed magnitude or a supplied confinement hypothesis. -/
-- Modern dependency score: 86/253 (M=86, H=167; transitive project theorems/axioms).
theorem gamma_band (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (x : BinaryTime T d.time_nonnegative) :
    Within (PositionValues.positionValue (gammaValue o E0 T tau L B s hE d x))
      (embed (PositionValues.zeroPoint,PositionValues.zeroPoint)) d.outer_radius ∧
      ∀ D, Within (PositionValues.positionValue (gammaValue o E0 T tau L B s hE d x))
        (embed (PositionValues.zeroPoint,PositionValues.zeroPoint)) D →
        Fraction.le d.inner_radius D := by
  induction x using Quotient.inductionOn with
  | _ b =>
    exact CompletionGeometry.position_band_realize
      (prefixName b o E0 T tau L B s hE d) d.inner_radius d.outer_radius
      (prefix_band b o E0 T tau L B s hE d)

/-- Changing the calibration or verified bounds keeps the same actual family. -/
-- Modern dependency score: 67/230 (M=67, H=163; transitive project theorems/axioms).
theorem gamma_conditions_independent (o : ForceClasses.CentralOracle)
    (E0 T tau L B tau' L' B' : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (e : GeneralForcePrefix.Conditions o E0 T tau' L' B' s hE)
    (x : BinaryTime T d.time_nonnegative) :
    gammaValue o E0 T tau L B s hE d x = gammaValue o E0 T tau' L' B' s hE e x := by
  induction x using Quotient.inductionOn with
  | _ b =>
    apply Quotient.sound
    intro eps heps
    refine ⟨0,fun j _ => ?_⟩
    exact distance_self_lt (prefixState b o E0 T s hE j) eps heps

-- Modern dependency score: 67/230 (M=67, H=163; transitive project theorems/axioms).
theorem gammaValue_address (b : Nat → Bool) (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    gammaValue o E0 T tau L B s hE d (Quotient.mk _ b) =
      realize (prefixName b o E0 T tau L B s hE d) := rfl

/-- A uniform-in-address geometric bound on actual prefix vertices. -/
-- Modern dependency score: 79/244 (M=79, H=165; transitive project theorems/axioms).
theorem prefix_value_bound (b : Nat → Bool) (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m : Nat) :
    Within (embed (prefixState b o E0 T s hE m))
      (gammaValue o E0 T tau L B s hE d (Quotient.mk _ b))
      (GeometricTail.tailCap (GeneralForcePrefix.coefficient E0 T tau L B s d.calibration_positive) m) :=
  TailValues.approximant_bound (prefixName b o E0 T tau L B s hE d)
    (GeneralForcePrefix.coefficient E0 T tau L B s d.calibration_positive)
    (GeneralForcePrefix.coefficient_nonnegative E0 T tau L B s hE d.time_nonnegative
      d.calibration_positive d.lipschitz.1 d.bound_nonnegative)
    (GeneralForcePrefix.adjacent_tail b o E0 T tau L B s hE d) m

-- Modern dependency score: 82/248 (M=82, H=166; transitive project theorems/axioms).
theorem prefix_uniform_convergence (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N ≤ m → ∀ b : Nat → Bool,
      Within (embed (prefixState b o E0 T s hE m))
        (gammaValue o E0 T tau L B s hE d (Quotient.mk _ b)) eps := by
  have hA := GeneralForcePrefix.coefficient_nonnegative E0 T tau L B s hE d.time_nonnegative
    d.calibration_positive d.lipschitz.1 d.bound_nonnegative
  obtain ⟨N,hN⟩ := duration_eventually_small
    (GeneralForcePrefix.coefficient E0 T tau L B s d.calibration_positive) eps hA heps
  refine ⟨N,fun m hm b => ?_⟩
  exact within_mono _ _ _ _ (Fraction.magnitudes.lt_implies_le (hN m hm))
    (prefix_value_bound b o E0 T tau L B s hE d m)

-- Modern dependency score: 76/243 (M=76, H=167; transitive project theorems/axioms).
theorem gamma_within (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (x y : BinaryTime T d.time_nonnegative) (R : Fraction)
    (hxy : TimeWithin T d.time_nonnegative x y R) :
    Within (gammaValue o E0 T tau L B s hE d x) (gammaValue o E0 T tau L B s hE d y)
      (Fraction.mul R (stateTimeFactor T tau B s d.calibration_positive)) := by
  induction x using Quotient.inductionOn with
  | _ b =>
    induction y using Quotient.inductionOn with
    | _ c =>
      change NameBound (prefixName b o E0 T tau L B s hE d)
        (prefixName c o E0 T tau L B s hE d)
        (Fraction.mul R (stateTimeFactor T tau B s d.calibration_positive))
      exact nameBound_scale (prefixName b o E0 T tau L B s hE d)
        (prefixName c o E0 T tau L B s hE d)
        (BinaryTime.timeName b T d.time_nonnegative) (BinaryTime.timeName c T d.time_nonnegative)
        (stateTimeFactor T tau B s d.calibration_positive) R
        (stateTimeFactor_nonnegative T tau B s d.time_nonnegative d.calibration_positive d.bound_nonnegative)
        (fun j => prefix_time_bound b c o E0 T tau L B s hE d j) hxy

noncomputable def timeTolerance (T tau B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hB : 0 ≤ B.num) (eps : Fraction) : Fraction :=
  Fraction.ofRat (factorDelta ((stateTimeFactor T tau B s ht)).toRat (eps.half).toRat ((Fraction.nonnegative_iff_toRat (stateTimeFactor T tau B s ht)).mp (stateTimeFactor_nonnegative T tau B s hT ht hB)))

-- Modern dependency score: 3/13 (M=3, H=10; transitive project theorems/axioms).
theorem timeTolerance_positive (T tau B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (ht : 0 < tau.num) (hB : 0 ≤ B.num) (eps : Fraction) (heps : 0 < eps.num) :
    0 < (timeTolerance T tau B s hT ht hB eps).num := (by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat (stateTimeFactor T tau B s ht)).mp (stateTimeFactor_nonnegative T tau B s hT ht hB))
        have hepsRat : 0 < (eps.half).toRat := (Fraction.positive_iff_toRat (eps.half)).mp heps
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos])

-- Modern dependency score: 79/246 (M=79, H=167; transitive project theorems/axioms).
theorem gamma_uniform_continuity (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (eps : Fraction) (heps : 0 < eps.num) (x y : BinaryTime T d.time_nonnegative)
    (hxy : TimeWithin T d.time_nonnegative x y
      (timeTolerance T tau B s d.time_nonnegative d.calibration_positive d.bound_nonnegative eps)) :
    Within (gammaValue o E0 T tau L B s hE d x) (gammaValue o E0 T tau L B s hE d y) eps.half :=
  within_mono _ _ _ _ ((by
      apply (Fraction.le_iff_toRat _ _).mpr
      change (Fraction.mul (Fraction.ofRat _) _).toRat ≤ Fraction.toRat _
      rw [Fraction.toRat_mul, Fraction.toRat_ofRat]
      exact HarmonicTimeRealization.factor_delta_weak _ _ ((Fraction.nonnegative_iff_toRat _).mp (stateTimeFactor_nonnegative T tau B s d.time_nonnegative d.calibration_positive d.bound_nonnegative)) ((Fraction.nonnegative_iff_toRat _).mp (by simpa only [Fraction.half] using Int.le_of_lt heps))))
    (gamma_within o E0 T tau L B s hE d x y _ hxy)

noncomputable def gammaPosition (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (x : BinaryTime T d.time_nonnegative) : PositionValues.PositionValue :=
  PositionValues.asPosition (gammaValue o E0 T tau L B s hE d x)

-- Modern dependency score: 85/252 (M=85, H=167; transitive project theorems/axioms).
theorem gammaPosition_within (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (x y : BinaryTime T d.time_nonnegative) (R : Fraction)
    (hxy : TimeWithin T d.time_nonnegative x y R) :
    Within (gammaPosition o E0 T tau L B s hE d x).val
      (gammaPosition o E0 T tau L B s hE d y).val
      (Fraction.mul R (stateTimeFactor T tau B s d.calibration_positive)) :=
  PositionValues.positionValue_within _ _ _ (gamma_within o E0 T tau L B s hE d x y R hxy)

-- Modern dependency score: 67/231 (M=67, H=164; transitive project theorems/axioms).
theorem left_endpoint_value (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    gammaValue o E0 T tau L B s hE d (leftTime T d.time_nonnegative) = embed s := by
  apply Quotient.sound
  intro eps heps
  refine ⟨0,fun j _ => ?_⟩
  change Fraction.lt (distance (prefixState leftAddress o E0 T s hE j) s) eps
  change Fraction.lt (distance
    (BoundedIteration.run (field o E0 hE j) (duration T j) s (ticks leftAddress j)) s) eps
  rw [show ticks leftAddress j = 0 from all_zero_ticks j]
  exact distance_self_lt s eps heps

-- Modern dependency score: 72/244 (M=72, H=172; transitive project theorems/axioms).
theorem zero_time_value (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (hT : T.num = 0) (x : BinaryTime T d.time_nonnegative) :
    gammaValue o E0 T tau L B s hE d x = embed s := by
  induction x using Quotient.inductionOn with
  | _ b =>
    apply Quotient.sound
    intro eps heps
    refine ⟨0,fun j _ => ?_⟩
    exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv ((distance_zero_iff_stateEquiv _ _).mpr
        (zero_time_prefix b o E0 T s hE hT j))) ((Fraction.positive_iff_zero_lt eps).mp heps)

/-- General E/G agreement at the end of the constructed window. -/
-- Modern dependency score: 71/235 (M=71, H=164; transitive project theorems/axioms).
theorem right_endpoint_value (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    gammaValue o E0 T tau L B s hE d (rightTime T d.time_nonnegative) =
      endpointValue o E0 T tau L B s hE d.toConditions := by
  apply Quotient.sound
  intro eps heps
  let C := stateTimeFactor T tau B s d.calibration_positive
  have hC := stateTimeFactor_nonnegative T tau B s d.time_nonnegative d.calibration_positive d.bound_nonnegative
  obtain ⟨N,hN⟩ := duration_eventually_small T (Fraction.ofRat (factorDelta (C).toRat (eps).toRat ((Fraction.nonnegative_iff_toRat C).mp hC)))
    d.time_nonnegative ((by
        apply (Fraction.positive_iff_toRat _).mpr
        change 0 < (Fraction.ofRat _).toRat
        rw [Fraction.toRat_ofRat]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hepsRat : 0 < (eps).toRat := (Fraction.positive_iff_toRat (eps)).mp heps
        (try dsimp only at hcoef hepsRat ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_pos]))
  refine ⟨N,fun j hj => ?_⟩
  have hop := count_step_bound o E0 T tau L B s hE d j (ticks rightAddress j) (ticks_lt_blocks rightAddress j)
  rw [right_ticks] at hop
  have hcal := Fraction.le_equiv_left (TimeCalibration.distance_symm tau _ _) hop
  have hgauge := Fraction.magnitudes.le_trans
    (TimeCalibration.uncalibrated_le_distance tau d.calibration_positive _ _)
    (Fraction.mul_le_mul_nonnegative_left hcal
      (Fraction.add (Fraction.ofInt 1) (TimeCalibration.inverse tau d.calibration_positive))
      (Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos)))
  have hb := Fraction.le_equiv_right hgauge (by
    change Fraction.equiv _ (Fraction.mul (duration T j) C)
    simp only [C,stateTimeFactor,Fraction.equiv,Fraction.mul]
    ac_nf)
  exact Fraction.magnitudes.lt_of_le_lt hb
    ((show Fraction.lt (Fraction.mul ((duration T j)) (C)) (eps) from by
        apply (Fraction.lt_iff_toRat _ _).mpr
        rw [Fraction.toRat_mul]
        have hcoef := ((Fraction.nonnegative_iff_toRat C).mp hC)
        have hdist := ((Fraction.nonnegative_iff_toRat (duration T j)).mp d.time_nonnegative)
        have hstrict := (Fraction.lt_iff_toRat _ _).mp (hN j hj)
        change (duration T j).toRat < (Fraction.ofRat _).toRat at hstrict
        rw [Fraction.toRat_ofRat] at hstrict
        (try dsimp only at hcoef hdist hstrict ⊢)
        grind only [HarmonicTimeRealization.factorDelta, Rat.lt_div_iff]))

end NewtonLimitDynamics.Polygon.GeneralForceTime
