import ModernLib.Polygon.GeneralForceTime
import ModernLib.Foundation.Polygon.SampledValues

-- Retain the 4.19 elaborator's unfolding behavior during the toolchain migration.
set_option backward.isDefEq.respectTransparency false

/-! Extend the actual sampled central force to completed positions with a
certified regional Cauchy representative. No whole-plane domain is required.
The same mesh precision used by the motion is retained. Error exhaustion and
Lipschitz comparisons construct the extension and its bounds; no desired
acceleration value or curve force equation is supplied. -/

namespace NewtonLimitDynamics.Polygon.CompletedForce
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic CauchyValues
open ForceClasses GeneralForcePrecision GeneralForceEndpoint HarmonicTimeRealization

def errorCoefficient (E0 : Fraction) : Fraction :=
  Fraction.add (Fraction.add E0 E0) E0

-- Modern dependency score: 1/6 (M=1, H=5; transitive project theorems/axioms).
theorem precisionError_le_sampleError (o : CentralOracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) :
    Fraction.le (o.error (precision o.toOracle E0 hE j)) (sampleError o E0 hE j) :=
  Fraction.magnitudes.le_trans (Fraction.le_add_nonnegative _ _ (o.error_nonnegative _))
    (Fraction.le_add_nonnegative _ _ (o.error_nonnegative _))

-- Modern dependency score: 4/16 (M=4, H=12; transitive project theorems/axioms).
theorem sampleError_tail (o : CentralOracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) :
    Fraction.le (sampleError o E0 hE j) (duration (errorCoefficient E0) j) := by
  have he := Fraction.magnitudes.lt_implies_le (precision_error o.toOracle E0 hE j)
  have ht := Fraction.add_le_add (Fraction.add_le_add he he) he
  apply Fraction.le_equiv_right ht
  simp only [errorCoefficient,GeometricTail.tailCap,duration,Fraction.equiv,
    Fraction.add,Int.add_mul,Int.mul_add]
  ac_nf

-- Modern dependency score: 5/20 (M=5, H=15; transitive project theorems/axioms).
theorem sampleError_vanishes (o : CentralOracle) (E0 : Fraction)
    (hE : 0 < E0.num) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j, N ≤ j → Fraction.lt (sampleError o E0 hE j) eps := by
  have hC : 0 ≤ (errorCoefficient E0).num := Fraction.nonnegative_add _ _
    (Fraction.nonnegative_add _ _ (Int.le_of_lt hE) (Int.le_of_lt hE)) (Int.le_of_lt hE)
  obtain ⟨N,hN⟩ := duration_eventually_small (errorCoefficient E0) eps hC heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt
    (sampleError_tail o E0 hE j) (hN j hj)⟩

noncomputable def family (o : CentralOracle) (E0 L : Fraction) (hE : 0 < E0.num)
    (hL : LipschitzOn o.toOracle L) : SampledValues.Family where
  sample := fun j s => accelerationState (field o E0 hE j s.1)
  region := fun s => o.region s.1
  coefficient := L
  coefficient_nonnegative := hL.1
  error := sampleError o E0 hE
  error_nonnegative := sampleError_nonnegative o E0 hE
  error_vanishes := sampleError_vanishes o E0 hE
  ordered_bound := by
    intro i j hij s t hs ht
    have hc := samples_comparison_contract o.toOracle L hL
      (precision o.toOracle E0 hE i) (precision o.toOracle E0 hE j)
      (precision_monotone o.toOracle E0 hE hij) s.1 t.1 hs ht
    have hb := Fraction.le_equiv_left (acceleration_distance _ _) hc
    have hp := Fraction.mul_le_mul_nonnegative_left
      (point_le_state (stateSub s t)) L hL.1
    have hs := Fraction.magnitudes.le_trans hb (Fraction.add_le_add_right hp _)
    exact Fraction.le_equiv_right hs
      (Fraction.add_equiv (Fraction.mul_comm _ _) (Fraction.equiv_refl _))

noncomputable def forceName (o : CentralOracle) (E0 L : Fraction) (hE : 0 < E0.num)
    (hL : LipschitzOn o.toOracle L) (a : EndpointCauchyName)
    (ha : ∀ n, o.region (a.approx n).1) : EndpointCauchyName :=
  SampledValues.sampledName (family o E0 L hE hL) a ha

noncomputable def forceValue (o : CentralOracle) (E0 L : Fraction) (hE : 0 < E0.num)
    (hL : LipschitzOn o.toOracle L) (x : Value)
    (hx : SampledValues.Admissible (fun q => o.region q.1) x) : Value :=
  SampledValues.sampledValue (family o E0 L hE hL) x hx

-- Modern dependency score: 25/79 (M=25, H=54; transitive project theorems/axioms).
theorem forceValue_realize (o : CentralOracle) (E0 L : Fraction) (hE : 0 < E0.num)
    (hL : LipschitzOn o.toOracle L) (a : EndpointCauchyName)
    (ha : ∀ n, o.region (a.approx n).1)
    (hx : SampledValues.Admissible (fun q => o.region q.1) (realize a)) :
    forceValue o E0 L hE hL (realize a) hx = realize (forceName o E0 L hE hL a ha) :=
  SampledValues.sampledValue_realize (family o E0 L hE hL) a ha hx

-- Modern dependency score: 32/89 (M=32, H=57; transitive project theorems/axioms).
theorem forceValue_within (o : CentralOracle) (E0 L : Fraction) (hE : 0 < E0.num)
    (hL : LipschitzOn o.toOracle L) (x y : Value)
    (hx : SampledValues.Admissible (fun q => o.region q.1) x)
    (hy : SampledValues.Admissible (fun q => o.region q.1) y)
    (R : Fraction) (hxy : Within x y R) :
    Within (forceValue o E0 L hE hL x hx) (forceValue o E0 L hE hL y hy)
      (Fraction.mul R L) :=
  SampledValues.sampledValue_within (family o E0 L hE hL) x y hx hy R hxy

-- Modern dependency score: 11/47 (M=11, H=36; transitive project theorems/axioms).
theorem position_admissible (o : CentralOracle) (x : Value)
    (hx : SampledValues.Admissible (fun q => o.region q.1) x) :
    SampledValues.Admissible (fun q => o.region q.1) (PositionValues.positionValue x) := by
  obtain ⟨a,rfl,ha⟩ := hx
  exact ⟨PositionValues.mapName PositionValues.positionState PositionValues.position_nonexpansive a,
    rfl,ha⟩

-- Modern dependency score: 31/85 (M=31, H=54; transitive project theorems/axioms).
theorem force_input_position (o : CentralOracle) (E0 L : Fraction) (hE : 0 < E0.num)
    (hL : LipschitzOn o.toOracle L) (x : Value)
    (hx : SampledValues.Admissible (fun q => o.region q.1) x) :
    forceValue o E0 L hE hL (PositionValues.positionValue x) (position_admissible o x hx) =
      forceValue o E0 L hE hL x hx := by
  obtain ⟨a,rfl,ha⟩ := hx
  change forceValue o E0 L hE hL
    (realize (PositionValues.mapName PositionValues.positionState PositionValues.position_nonexpansive a)) _ = _
  rw [forceValue_realize o E0 L hE hL
    (PositionValues.mapName PositionValues.positionState PositionValues.position_nonexpansive a)
    (fun n => ha n),forceValue_realize o E0 L hE hL a ha]
  rfl

-- Modern dependency score: 30/84 (M=30, H=54; transitive project theorems/axioms).
theorem force_output_position (o : CentralOracle) (E0 L : Fraction) (hE : 0 < E0.num)
    (hL : LipschitzOn o.toOracle L) (x : Value)
    (hx : SampledValues.Admissible (fun q => o.region q.1) x) :
    PositionValues.positionValue (forceValue o E0 L hE hL x hx) =
      forceValue o E0 L hE hL x hx := by
  obtain ⟨a,rfl,ha⟩ := hx
  rw [forceValue_realize o E0 L hE hL a ha]
  rfl

noncomputable def acceleration (o : CentralOracle) (E0 L : Fraction) (hE : 0 < E0.num)
    (hL : LipschitzOn o.toOracle L) (x : PositionValues.PositionValue)
    (hx : SampledValues.Admissible (fun q => o.region q.1) x.val) : PositionValues.PositionValue :=
  ⟨forceValue o E0 L hE hL x.val hx,force_output_position o E0 L hE hL x.val hx⟩

/-- Agreement with the retained force value at every rational point. The mesh
precision may remain constant; no premise that precision(j) >= j is used. -/
-- Modern dependency score: 28/82 (M=28, H=54; transitive project theorems/axioms).
theorem force_rational_agreement (o : CentralOracle) (E0 L : Fraction)
    (hE : 0 < E0.num) (hL : LipschitzOn o.toOracle L)
    (s : Point × Point) (hs : o.region s.1) :
    forceValue o E0 L hE hL (embed s) (SampledValues.admissible_embed _ s hs) =
      accelerationValue o.toOracle s.1 hs := by
  change forceValue o E0 L hE hL (realize (constantName s)) _ = accelerationValue o.toOracle s.1 hs
  rw [forceValue_realize o E0 L hE hL (constantName s) (fun _ => hs)]
  apply Quotient.sound
  intro eps heps
  obtain ⟨N,hN⟩ := o.error_vanishes eps heps
  obtain ⟨M,hM⟩ := sampleError_vanishes o E0 hE eps heps
  refine ⟨max N M,fun j hj => ?_⟩
  let q := precision o.toOracle E0 hE j
  by_cases hq : q ≤ j
  · have hc := o.coherent q j hq s.1 hs
    have he := precisionError_le_sampleError o E0 hE j
    exact Fraction.magnitudes.lt_of_le_lt (Fraction.magnitudes.le_trans hc he) (hM j (by omega))
  · exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_equiv_left (stateSub_norm_symm _ _)
        (o.coherent j q (by omega) s.1 hs)) (hN j (by omega))

/-- Precision scales and valid Lipschitz bounds do not change the completed
force. Independence of the motion from these choices is a separate theorem. -/
-- Modern dependency score: 27/81 (M=27, H=54; transitive project theorems/axioms).
theorem force_precision_independent (o : CentralOracle) (E0 E1 L L' : Fraction)
    (hE : 0 < E0.num) (hE' : 0 < E1.num)
    (hL : LipschitzOn o.toOracle L) (hL' : LipschitzOn o.toOracle L')
    (x : Value) (hx : SampledValues.Admissible (fun q => o.region q.1) x) :
    forceValue o E0 L hE hL x hx = forceValue o E1 L' hE' hL' x hx := by
  obtain ⟨a,rfl,ha⟩ := hx
  rw [forceValue_realize o E0 L hE hL a ha,forceValue_realize o E1 L' hE' hL' a ha]
  apply Quotient.sound
  intro eps heps
  obtain ⟨N,hN⟩ := sampleError_vanishes o E0 hE eps heps
  obtain ⟨M,hM⟩ := sampleError_vanishes o E1 hE' eps heps
  refine ⟨max N M,fun j hj => ?_⟩
  let q := precision o.toOracle E0 hE j
  let q' := precision o.toOracle E1 hE' j
  by_cases hq : q ≤ q'
  · exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.magnitudes.le_trans (o.coherent q q' hq (a.approx j).1 (ha j))
        (precisionError_le_sampleError o E0 hE j)) (hN j (by omega))
  · exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_equiv_left (stateSub_norm_symm _ _)
        (Fraction.magnitudes.le_trans
          (o.coherent q' q (by omega) (a.approx j).1 (ha j))
          (precisionError_le_sampleError o E1 hE' j))) (hM j (by omega))

def curveErrorCoefficient (A E0 L : Fraction) : Fraction :=
  Fraction.add (Fraction.mul A L) (errorCoefficient E0)

-- Modern dependency score: 96/265 (M=96, H=169; transitive project theorems/axioms).
theorem prefix_force_bound (b : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (j : Nat) :
    Within (embed (accelerationState (field o E0 hE j
      (GeneralForcePrefix.prefixState b o E0 T s hE j).1)))
      (forceValue o E0 L hE d.lipschitz
        (GeneralForceTime.gammaValue o E0 T tau L B s hE d (Quotient.mk _ b))
        (GeneralForceTime.gamma_admissible o E0 T tau L B s hE d (Quotient.mk _ b)))
      (duration (curveErrorCoefficient
        (GeneralForcePrefix.coefficient E0 T tau L B s d.calibration_positive) E0 L) j) := by
  let A := GeneralForcePrefix.coefficient E0 T tau L B s d.calibration_positive
  have hb := SampledValues.sampled_approximant_bound (family o E0 L hE d.lipschitz)
    (GeneralForcePrefix.prefixName b o E0 T tau L B s hE d)
    (GeneralForceTime.prefix_region b o E0 T tau L B s hE d)
    (GeneralForceTime.gamma_admissible o E0 T tau L B s hE d (Quotient.mk _ b)) j (GeometricTail.tailCap A j)
    (GeneralForceTime.prefix_value_bound b o E0 T tau L B s hE d j)
  apply within_mono _ _ _ _ ?_ hb
  have ht := Fraction.add_le_add_left (sampleError_tail o E0 hE j)
    (Fraction.mul (GeometricTail.tailCap A j) L)
  apply Fraction.le_equiv_right ht
  simp only [A,curveErrorCoefficient,GeometricTail.tailCap,duration,Fraction.equiv,
    Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
  ac_nf

/-- Uniform convergence of actual polygon force samples to the force at the
constructed completed positions. This is not yet the acceleration equation. -/
-- Modern dependency score: 97/266 (M=97, H=169; transitive project theorems/axioms).
theorem prefix_force_uniform_convergence (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j, N ≤ j → ∀ b : Nat → Bool,
      Within (embed (accelerationState (field o E0 hE j
        (GeneralForcePrefix.prefixState b o E0 T s hE j).1)))
        (forceValue o E0 L hE d.lipschitz
          (GeneralForceTime.gammaValue o E0 T tau L B s hE d (Quotient.mk _ b))
          (GeneralForceTime.gamma_admissible o E0 T tau L B s hE d (Quotient.mk _ b))) eps := by
  let A := GeneralForcePrefix.coefficient E0 T tau L B s d.calibration_positive
  have hA := GeneralForcePrefix.coefficient_nonnegative E0 T tau L B s hE d.time_nonnegative
    d.calibration_positive d.lipschitz.1 d.bound_nonnegative
  have hC : 0 ≤ (curveErrorCoefficient A E0 L).num :=
    Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hA d.lipschitz.1)
      (Fraction.nonnegative_add _ _
        (Fraction.nonnegative_add _ _ (Int.le_of_lt hE) (Int.le_of_lt hE)) (Int.le_of_lt hE))
  obtain ⟨N,hN⟩ := duration_eventually_small (curveErrorCoefficient A E0 L) eps hC heps
  exact ⟨N,fun j hj b => within_mono _ _ _ _
    (Fraction.magnitudes.lt_implies_le (hN j hj)) (prefix_force_bound b o E0 T tau L B s hE d j)⟩

end NewtonLimitDynamics.Polygon.CompletedForce
