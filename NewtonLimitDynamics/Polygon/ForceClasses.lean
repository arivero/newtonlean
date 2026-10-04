import NewtonLimitDynamics.Polygon.PositionValues
import NewtonLimitDynamics.Polygon.InertialDefect
import NewtonLimitDynamics.Polygon.StripArea
import BarrowLib.Polygon.FiniteEstimates
import BarrowLib.Polygon.BoundedIteration
import BarrowLib.Polygon.FiniteAccumulation

/-!
Uniform rational approximations to possibly irrational accelerations on an
explicit region. These are contracts on the force data, not assertions that
an impulse polygon converges. Realized sample values are constructed Cauchy
quotients. Historical editions and action diagnostics are not premises here.
-/

namespace NewtonLimitDynamics.Polygon.ForceClasses

open NewtonLimitDynamics
open TimeSubdivision PointBounds CentralSchedule HarmonicStability
open HarmonicComparison HarmonicDyadic CauchyValues

/-- Store a rational acceleration in the position slots of a state name. -/
def accelerationState (p : Point) : Point × Point :=
  PositionValues.positionState (p, p)

/-- Uniform sampling error is proved for the force oracle, not the motion. -/
structure Oracle where
  region : Point → Prop
  sample : Nat → Field
  error : Nat → Fraction
  error_nonnegative : ∀ n, 0 ≤ (error n).num
  error_vanishes : ∀ eps : Fraction, 0 < eps.num →
    ∃ N : Nat, ∀ n, N ≤ n → Fraction.lt (error n) eps
  coherent : ∀ i j, i ≤ j → ∀ p, region p →
    Fraction.le (distance (accelerationState (sample i p))
      (accelerationState (sample j p))) (error i)

/-- A central oracle also records the inward sense, absent from collinearity. -/
structure CentralOracle extends Oracle where
  inward : ∀ n p, ∃ k : Fraction, 0 ≤ k.num ∧
    pointEquiv (sample n p) (linearField k p)

/-- Every approximating finite polygon is central, even outside confinement. -/
theorem sample_central (o : CentralOracle) (n : Nat) : central (o.sample n) := by
  intro p
  obtain ⟨k, _, hk⟩ := o.inward n p
  exact Fraction.equiv_trans
    (InertialDefect.det_congr ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩ hk)
    (linearField_central k p)

theorem sampled_finite_area_law (o : CentralOracle) (n : Nat)
    (ds : List Fraction) (s : Point × Point) :
    Fraction.equiv (swept (o.sample n) ds s)
      (Fraction.mul (elapsed ds) (momentum s)) :=
  swept_eq (o.sample n) (sample_central o n) ds s

/-- Pointwise force values are constructed from the uniform-error contract. -/
def accelerationName (o : Oracle) (p : Point) (hp : o.region p) :
    EndpointCauchyName where
  approx := fun n => accelerationState (o.sample n p)
  cauchy := by
    intro eps heps
    obtain ⟨N, hN⟩ := o.error_vanishes eps heps
    refine ⟨N, ?_⟩
    intro m n hm hn
    by_cases hmn : m ≤ n
    · exact Fraction.magnitudes.lt_of_le_lt (o.coherent m n hmn p hp) (hN m hm)
    · have hnm : n ≤ m := by omega
      have he := stateSub_norm_symm
        (accelerationState (o.sample m p)) (accelerationState (o.sample n p))
      exact Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_equiv_left he (o.coherent n m hnm p hp)) (hN n hn)

def accelerationValue (o : Oracle) (p : Point) (hp : o.region p) : Value :=
  realize (accelerationName o p hp)

theorem acceleration_approximants_converge (o : Oracle) (p : Point)
    (hp : o.region p) (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ n, N ≤ n →
      Within (embed (accelerationState (o.sample n p)))
        (accelerationValue o p hp) eps :=
  constant_approximants_converge (accelerationName o p hp) eps heps

/-- Rounding error remains additive; individual samples need not be Lipschitz. -/
def LipschitzOn (o : Oracle) (L : Fraction) : Prop :=
  0 ≤ L.num ∧ ∀ n p q, o.region p → o.region q →
    Fraction.le (pointNorm (pointSub (o.sample n p) (o.sample n q)))
      (Fraction.add (Fraction.mul L (pointNorm (pointSub p q)))
        (Fraction.add (o.error n) (o.error n)))

/-- Continuous classes have a uniform modulus on the named confined region. -/
def ContinuousOn (o : Oracle) : Prop :=
  ∀ eps : Fraction, 0 < eps.num → ∃ delta : Fraction, 0 < delta.num ∧
    ∃ N : Nat, ∀ n p q, N ≤ n → o.region p → o.region q →
      Fraction.lt (pointNorm (pointSub p q)) delta →
      Fraction.lt (pointNorm (pointSub (o.sample n p) (o.sample n q))) eps

def BoundedOn (o : Oracle) (B : Fraction) : Prop :=
  0 ≤ B.num ∧ ∀ n p, o.region p → Fraction.le (pointNorm (o.sample n p)) B

theorem acceleration_distance (p q : Point) :
    Fraction.equiv (distance (accelerationState p) (accelerationState q))
      (FiniteEstimates.pointDistance p q) := by
  change Fraction.equiv
    (Fraction.add (FiniteEstimates.pointDistance p q) (Fraction.ofInt 0))
    (FiniteEstimates.pointDistance p q)
  exact Fraction.add_zero _

/-- Uniform force coherence also controls successive precisions at the same
rational point. No exact force value is presumed rational. -/
theorem sample_point_error (o : Oracle) (i j : Nat) (hij : i ≤ j)
    (p : Point) (hp : o.region p) :
    Fraction.le (FiniteEstimates.pointDistance (o.sample i p) (o.sample j p))
      (o.error i) :=
  Fraction.le_equiv_left (Fraction.equiv_symm (acceleration_distance _ _))
    (o.coherent i j hij p hp)

/-- A global comparison contract follows on a globally declared region.
Region-local applications must separately prove the locations lie in it. -/
theorem samples_comparison_contract (o : Oracle) (L : Fraction)
    (hL : LipschitzOn o L) (hR : ∀ p, o.region p)
    (i j : Nat) (hij : i ≤ j) :
    FiniteEstimates.comparisonContract (o.sample i) (o.sample j) L
      (Fraction.add (Fraction.add (o.error i) (o.error i)) (o.error i)) := by
  intro p q
  have ht := FiniteEstimates.pointDistance_triangle (o.sample i p)
    (o.sample i q) (o.sample j q)
  have hs := Fraction.add_le_add (hL.2 i p q (hR p) (hR q))
    (sample_point_error o i j hij q (hR q))
  apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans ht hs)
  simp only [Fraction.equiv, Fraction.add, Int.add_mul, Int.mul_add]
  ac_nf

/-- Distance is encoded by its square; no rational square root is assumed. -/
def DistanceOnly (o : CentralOracle) : Prop :=
  ∀ n p q, Fraction.equiv (dot p p) (dot q q) →
    ∃ k : Fraction, 0 ≤ k.num ∧
      pointEquiv (o.sample n p) (linearField k p) ∧
      pointEquiv (o.sample n q) (linearField k q)

/-- Class (a)'s force regularity. Potential identification is a separate step. -/
def ClassAForce (o : CentralOracle) : Prop :=
  DistanceOnly o ∧ ∃ L : Fraction, LipschitzOn o.toOracle L

/-- Class (b) permits direction dependence; nonconservativity needs its own test. -/
def ClassBForce (o : CentralOracle) : Prop := ContinuousOn o.toOracle

def ClassCForce (o : CentralOracle) : Prop :=
  DistanceOnly o ∧ ContinuousOn o.toOracle

/-- No regularity premise is used by the finite area law. -/
def ClassDForce (_o : CentralOracle) : Prop := True

/-- An exactly rational law is a zero-error instance of the sampling interface. -/
def exactOracle (a : Field) : Oracle where
  region := fun _ => True
  sample := fun _ => a
  error := fun _ => Fraction.ofInt 0
  error_nonnegative := fun _ => by decide
  error_vanishes := by
    intro eps heps
    exact ⟨0, fun _ _ => (Fraction.positive_iff_zero_lt eps).mp heps⟩
  coherent := by
    intro _ _ _ _p _
    exact Fraction.le_of_equiv (HarmonicAccumulation.stateSub_self_norm_zero _)

theorem exact_accelerationValue (a : Field) (p : Point) :
    accelerationValue (exactOracle a) p True.intro =
      embed (accelerationState (a p)) := rfl

def harmonicOracle (w : Fraction) (hw : 0 ≤ w.num) : CentralOracle where
  toOracle := exactOracle (linearField w)
  inward := fun _ _p => ⟨w, hw, ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩

theorem harmonic_distance_only (w : Fraction) (hw : 0 ≤ w.num) :
    DistanceOnly (harmonicOracle w hw) := by
  intro _ p q _
  exact ⟨w, hw, ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
    ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩

theorem harmonic_comparison_contract (w : Fraction) :
    FiniteEstimates.comparisonContract (linearField w) (linearField w)
      w.abs (Fraction.ofInt 0) := linearField_comparison_contract w

theorem harmonic_class_a_force (w : Fraction) (hw : 0 ≤ w.num) :
    ClassAForce (harmonicOracle w hw) := by
  refine ⟨harmonic_distance_only w hw, w.abs, Fraction.abs_num_nonnegative w, ?_⟩
  intro n p q _ _
  have h := harmonic_comparison_contract w p q
  apply Fraction.le_equiv_right h
  exact Fraction.add_equiv (Fraction.equiv_refl _)
    (Fraction.equiv_symm (Fraction.add_zero (Fraction.ofInt 0)))

/-- The permitted centre-at-infinity instance is a uniform parallel field. -/
def parallelOracle (a : Point) : Oracle := exactOracle (fun _ => a)

theorem parallel_cell (a : Point) (h : Fraction) (s : Point × Point) :
    cell ((parallelOracle a).sample 0) h s = endKick h s a := rfl

/-- Multiplication by the fixed force magnitude converts this determinant
into the velocity component perpendicular to the parallel force. -/
theorem parallel_transverse_cell (a : Point) (h : Fraction) (s : Point × Point) :
    Fraction.equiv (det (cell (fun _ => a) h s).2 a) (det s.2 a) :=
  StripArea.det_kick_direction_constant h s.2 a

theorem parallel_transverse_schedule (a : Point) (ds : List Fraction)
    (s : Point × Point) :
    Fraction.equiv (det (schedule (fun _ => a) ds s).2 a) (det s.2 a) := by
  induction ds generalizing s with
  | nil => exact Fraction.equiv_refl _
  | cons h ds ih =>
      exact Fraction.equiv_trans (ih (cell (fun _ => a) h s))
        (parallel_transverse_cell a h s)

/-- Identify the generic forward iterates with the actual finite schedule. -/
theorem run_eq_schedule (a : Field) (h : Fraction) (s : Point × Point) (n : Nat) :
    BoundedIteration.run a h s n = schedule a (List.replicate n h) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, schedule]
      rw [← ih]
      exact (BoundedIteration.run_commute a h s n).symm

theorem bounded_samples_of_confined (o : Oracle) (j : Nat) (h : Fraction)
    (s : Point × Point) (B : Fraction) (n : Nat) (hB : BoundedOn o B)
    (hR : ∀ i : Nat, i < n → o.region (BoundedIteration.run (o.sample j) h s (i+1)).1) :
    BoundedIteration.BoundedSamples (o.sample j) h s B n :=
  fun i hi => hB.2 j _ (hR i hi)

/-- These actual polygon bounds apply also to continuous, non-Lipschitz laws;
confinement is an explicit premise, not a conclusion of continuity. -/
theorem sampled_polygon_velocity_bound (o : Oracle) (j : Nat) (h : Fraction)
    (s : Point × Point) (B : Fraction) (n : Nat) (hh : 0 ≤ h.num)
    (hB : BoundedOn o B)
    (hR : ∀ i : Nat, i < n → o.region (BoundedIteration.run (o.sample j) h s (i+1)).1) :
    Fraction.le (pointNorm (schedule (o.sample j) (List.replicate n h) s).2)
      (Fraction.add (pointNorm s.2) (Fraction.mul (BoundedIteration.time h n) B)) := by
  rw [← run_eq_schedule]
  exact BoundedIteration.velocity_bound (o.sample j) h s B hh n
    (bounded_samples_of_confined o j h s B n hB hR)

theorem sampled_polygon_position_bound (o : Oracle) (j : Nat) (h : Fraction)
    (s : Point × Point) (B : Fraction) (n : Nat) (hh : 0 ≤ h.num)
    (hB : BoundedOn o B)
    (hR : ∀ i : Nat, i < n → o.region (BoundedIteration.run (o.sample j) h s (i+1)).1) :
    Fraction.le (pointNorm (schedule (o.sample j) (List.replicate n h) s).1)
      (BoundedIteration.positionCap h s B n) := by
  rw [← run_eq_schedule]
  exact BoundedIteration.position_bound (o.sample j) h s B hh hB.1 n
    (bounded_samples_of_confined o j h s B n hB hR)

theorem sampled_polygon_state_bound (o : Oracle) (j : Nat) (h : Fraction)
    (s : Point × Point) (B T : Fraction) (n : Nat) (hh : 0 ≤ h.num)
    (hT : 0 ≤ T.num) (hB : BoundedOn o B)
    (ht : Fraction.le (BoundedIteration.time h n) T)
    (hR : ∀ i : Nat, i < n → o.region (BoundedIteration.run (o.sample j) h s (i+1)).1) :
    Fraction.le (stateNorm (schedule (o.sample j) (List.replicate n h) s))
      (Fraction.add (BoundedIteration.uniformPositionCap T s B)
        (Fraction.add (pointNorm s.2) (Fraction.mul T B))) := by
  rw [← run_eq_schedule]
  exact BoundedIteration.state_bound_at_time (o.sample j) h s B T hh hB.1 hT n
    (bounded_samples_of_confined o j h s B n hB hR) ht

/-- Merely continuous laws give a vanishing local refinement source.
The modulus controls all three actual arrival points. This is a consistency
estimate, distinct from stability, full-family convergence or uniqueness. -/
theorem continuous_local_refinement (o : Oracle) (hC : ContinuousOn o)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ delta : Fraction, 0 < delta.num ∧ ∃ N : Nat,
    ∀ (j : Nat) (h B : Fraction) (s : Point × Point), N ≤ j → BoundedOn o B →
      o.region (FiniteEstimates.cell (o.sample j) h s).1 →
      o.region (FiniteEstimates.oneFull (o.sample j) h s).1 →
      o.region (FiniteEstimates.twoHalf (o.sample j) h s).1 →
      Fraction.lt (Fraction.mul h.abs (pointNorm s.2)) delta →
      Fraction.lt (Fraction.mul (Fraction.mul h h).abs B) delta →
      Fraction.le
        (FiniteEstimates.stateDistance (FiniteEstimates.twoHalf (o.sample j) h s)
          (FiniteEstimates.oneFull (o.sample j) h s))
        (Fraction.add (Fraction.mul (Fraction.mul h h).abs B)
          (Fraction.mul h.abs (Fraction.add eps eps))) := by
  obtain ⟨delta, hdelta, N, hN⟩ := hC eps heps
  refine ⟨delta, hdelta, N, ?_⟩
  intro j h B s hj hB hfirst hfull hfine hv hf
  have hb := hB.2 j _ hfirst
  have hd₁ := Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (FiniteEstimates.first_to_full_distance (o.sample j) h s)) hv
  have hd₂ := Fraction.magnitudes.lt_of_le_lt
    (FiniteEstimates.twoHalf_position_error (o.sample j) h B s hb) hf
  have hs₁ := Fraction.magnitudes.lt_implies_le
    (hN j _ _ hj hfirst hfull hd₁)
  have hs₂ := Fraction.magnitudes.lt_implies_le
    (hN j _ _ hj hfine hfull hd₂)
  exact Fraction.add_le_add
    (FiniteEstimates.twoHalf_position_error (o.sample j) h B s hb)
    (FiniteEstimates.twoHalf_velocity_sample_error (o.sample j) h eps eps s hs₁ hs₂)

/-- Successive oracle precisions instantiate the actual mesh comparison.
The global-region premise is explicit; an annulus requires local confinement
for the additional comparison arrivals before this theorem applies. -/
theorem sampled_uniform_refinement (o : Oracle) (j : Nat)
    (h L B V : Fraction) (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) (hL : LipschitzOn o L)
    (hR : ∀ p, o.region p) (hB : BoundedOn o B) (hV : 0 ≤ V.num)
    (hs : FiniteAccumulation.SmallWindow h L n)
    (hvel : ∀ k, k < n → Fraction.le
      (pointNorm (FiniteAccumulation.coarseAt (o.sample j) h s k).2) V) :
    Fraction.le
      (FiniteEstimates.stateDistance (FiniteAccumulation.fineAt (o.sample (j+1)) h s n)
        (FiniteAccumulation.coarseAt (o.sample j) h s n))
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (FiniteAccumulation.count n)
          (FiniteAccumulation.uniformBlockSource h L
            (Fraction.add (Fraction.add (o.error j) (o.error j)) (o.error j)) B V))) := by
  let E := Fraction.add (Fraction.add (o.error j) (o.error j)) (o.error j)
  have hE : 0 ≤ E.num := Fraction.nonnegative_add _ _
    (Fraction.nonnegative_add _ _ (o.error_nonnegative j) (o.error_nonnegative j))
    (o.error_nonnegative j)
  have hcross := FiniteEstimates.comparisonContract_reverse _ _ L E
    (samples_comparison_contract o L hL hR j (j+1) (by omega))
  exact FiniteAccumulation.cross_actual_uniform_error (o.sample (j+1)) (o.sample j)
    h L E B V s n hh hL.1 hE hB.1 hV hs hcross
    (samples_comparison_contract o L hL hR j j (by omega))
    (fun k _ => hB.2 j _ (hR _)) hvel

end NewtonLimitDynamics.Polygon.ForceClasses
