import ModernLib.Polygon.GeneralForceEndpoint

/-! The harmonic family is an actual instance of the general sampled endpoint
construction. Its finite acceleration bounds are derived on the short family,
not postulated globally. The old endpoint names and values remain available. -/

namespace NewtonLimitDynamics.Polygon.HarmonicGeneralEndpoint
open NewtonLimitDynamics
open TimeSubdivision PointBounds ForceClasses HarmonicStability HarmonicDyadic


/-- Precision selection has no effect on a zero-error exact law. -/
-- Modern dependency score: 1/15 (M=1, H=14; transitive project theorems/axioms).
theorem harmonic_field (w E0 : Fraction) (hw : 0 ≤ w.num) (hE : 0 < E0.num) (j : Nat) :
    GeneralForceEndpoint.field (harmonicOracle w hw) E0 hE j = linearField w := rfl

def harmonicBound (w : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul w.abs (Fraction.mul (Fraction.ofInt 4) (stateNorm s))

-- Modern dependency score: 0/4 (M=0, H=4; transitive project theorems/axioms).
theorem harmonicBound_nonnegative (w : Fraction) (s : Point × Point) :
    0 ≤ (harmonicBound w s).num := Fraction.nonnegative_mul _ _
  (Fraction.abs_num_nonnegative w)
  (Fraction.nonnegative_mul _ _ (by decide) (stateNorm_nonnegative s))

-- Modern dependency score: 0/9 (M=0, H=9; transitive project theorems/axioms).
theorem linear_sample_norm (w : Fraction) (p : Point) :
    Fraction.equiv (pointNorm (linearField w p)) (Fraction.mul w.abs (pointNorm p)) :=
  Fraction.equiv_trans (pointNorm_scale (negF w) p)
    (Fraction.mul_equiv (Fraction.abs_neg w) (Fraction.equiv_refl _))

-- Modern dependency score: 1/16 (M=1, H=15; transitive project theorems/axioms).
theorem linear_sample_bound (w : Fraction) (s : Point × Point) (p : Point)
    (hp : Fraction.le (pointNorm p) (Fraction.mul (Fraction.ofInt 4) (stateNorm s))) :
    Fraction.le (pointNorm (linearField w p)) (harmonicBound w s) :=
  Fraction.le_equiv_left (linear_sample_norm w p)
    (Fraction.mul_le_mul_nonnegative_left hp w.abs (Fraction.abs_num_nonnegative w))

-- Modern dependency score: 30/74 (M=30, H=44; transitive project theorems/axioms).
theorem full_run_state_bound (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (j k : Nat) (hk : k ≤ blocks j) :
    Fraction.le
      (stateNorm (BoundedIteration.run (linearField w)
        (Fraction.add (duration T (j+1)) (duration T (j+1))) s k))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) := by
  rw [run_eq_schedule,HarmonicAccumulation.coarseAt_schedule]
  exact HarmonicUniform.coarse_state_le_two w (duration T (j+1)) s k hT
    (HarmonicUniform.smallTime_prefix w (duration T (j+1)) k (blocks j) hT hk
      (dyadic_smallTime w T j hs))

-- Modern dependency score: 0/4 (M=0, H=4; transitive project theorems/axioms).
theorem two_to_four (s : Point × Point) :
    Fraction.le (Fraction.mul (Fraction.ofInt 2) (stateNorm s))
      (Fraction.mul (Fraction.ofInt 4) (stateNorm s)) :=
  Fraction.mul_le_mul_nonnegative (by unfold Fraction.le Fraction.ofInt; decide) (stateNorm s) (stateNorm_nonnegative s)

-- Modern dependency score: 0/14 (M=0, H=14; transitive project theorems/axioms).
theorem time_le_one (w T : Fraction) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le T (Fraction.ofInt 1) := by
  have hone := Fraction.le_add_nonnegative (Fraction.ofInt 1) w.abs
    (Fraction.abs_num_nonnegative w)
  have hm := Fraction.mul_le_mul_nonnegative_left hone T hT
  have he : Fraction.equiv (Fraction.mul T (Fraction.ofInt 1)) T := by
    simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
  have ht := Fraction.magnitudes.le_trans
    (Fraction.le_equiv_left (Fraction.equiv_symm he) hm) hs
  exact Fraction.magnitudes.le_trans ht (by
    change Fraction.le (⟨1,2,by decide⟩ : Fraction) (Fraction.ofInt 1)
    unfold Fraction.le Fraction.ofInt
    decide)

-- Modern dependency score: 33/84 (M=33, H=51; transitive project theorems/axioms).
theorem shadow_position_bound (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (j k : Nat) (hk : k < blocks j) :
    Fraction.le
      (pointNorm (FiniteEstimates.cell (linearField w) (duration T (j+1))
        (FiniteAccumulation.coarseAt (linearField w) (duration T (j+1)) s k)).1)
      (Fraction.mul (Fraction.ofInt 4) (stateNorm s)) := by
  let t := FiniteAccumulation.coarseAt (linearField w) (duration T (j+1)) s k
  have ht : Fraction.le (stateNorm t) (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) := by
    dsimp only [t]
    rw [CalibratedRefinement.coarseAt_eq_run]
    exact full_run_state_bound w T s hT hs j k (Nat.le_of_lt hk)
  have hp := Fraction.magnitudes.le_trans (point_le_state t) ht
  have hv := Fraction.magnitudes.le_trans (velocity_le_state t) ht
  have hh : Fraction.le (duration T (j+1)).abs (Fraction.ofInt 1) := by
    rw [Fraction.abs_eq_of_nonnegative (duration T (j+1)) hT]
    exact Fraction.magnitudes.le_trans (GeneralForceEndpoint.duration_le_window T hT (j+1)) (time_le_one w T hT hs)
  have hmv := Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative_left hv (duration T (j+1)).abs (Fraction.abs_num_nonnegative _))
    (Fraction.mul_le_mul_nonnegative hh (Fraction.mul (Fraction.ofInt 2) (stateNorm s))
      (Fraction.nonnegative_mul _ _ (by decide) (stateNorm_nonnegative s)))
  have hc := Fraction.magnitudes.le_trans (FiniteEstimates.cell_position_growth (linearField w) (duration T (j+1)) t)
    (Fraction.add_le_add hp hmv)
  apply Fraction.le_equiv_right hc
  simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    show (4 : Int) = 2+2 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

/-- The retained harmonic window supplies a finite regional ball budget. -/
-- Modern dependency score: 1/25 (M=1, H=24; transitive project theorems/axioms).
theorem harmonic_band_budget (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le (Fraction.add (pointNorm s.1)
      (Fraction.mul T (GeneralForceEndpoint.velocityCap T (harmonicBound w s) s)))
      (Fraction.mul (Fraction.ofInt 4) (stateNorm s)) := by
  have hw1 := Fraction.le_equiv_right
    (Fraction.le_add_nonnegative w.abs (Fraction.ofInt 1) (by decide))
    (Fraction.add_comm _ _)
  have hTw := Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative_left hw1 T hT) hs
  have hC : 0 ≤ (Fraction.mul (Fraction.ofInt 4) (stateNorm s)).num :=
    Fraction.nonnegative_mul _ _ (by decide) (stateNorm_nonnegative s)
  have hTB := Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))
      (Fraction.mul_le_mul_nonnegative hTw _ hC))
    (show Fraction.equiv (Fraction.mul (⟨1,2,by decide⟩ : Fraction)
      (Fraction.mul (Fraction.ofInt 4) (stateNorm s)))
      (Fraction.mul (Fraction.ofInt 2) (stateNorm s)) by
      simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt]
      ac_nf)
  have hV : Fraction.le (GeneralForceEndpoint.velocityCap T (harmonicBound w s) s)
      (Fraction.mul (Fraction.ofInt 3) (stateNorm s)) :=
    Fraction.le_equiv_right (Fraction.add_le_add (velocity_le_state s) hTB)
      (by simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        show (3 : Int)=1+2 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]; ac_nf)
  have hTV := Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative_left hV T hT)
    (Fraction.mul_le_mul_nonnegative (time_le_one w T hT hs)
      (Fraction.mul (Fraction.ofInt 3) (stateNorm s))
      (Fraction.nonnegative_mul _ _ (by decide) (stateNorm_nonnegative s)))
  apply Fraction.le_equiv_right (Fraction.add_le_add (point_le_state s) hTV)
  simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    show (4 : Int)=1+3 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

/-- Every force-data premise of the general construction is derived for the old harmonic window. -/
def conditions (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    GeneralForceEndpoint.Conditions (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs (harmonicBound w s) s hE where
  calibration_positive := by decide
  lipschitz := harmonic_lipschitz_on w hw
  window := by
    apply Fraction.le_equiv_left (b := Fraction.mul T (Fraction.add (Fraction.ofInt 1) w.abs)) _ hs
    apply Fraction.mul_equiv (Fraction.equiv_refl _)
    simp only [TimeCalibration.rate,TimeCalibration.inverse,Fraction.equiv,Fraction.add,
      Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
  inner_radius := Fraction.ofInt 0
  outer_radius := Fraction.mul (Fraction.ofInt 4) (stateNorm s)
  frame := RegionConfinement.ball_frame _ T (harmonicBound w s) _ s hT
    (harmonicBound_nonnegative w s) (harmonic_band_budget w T s hT hs)
    (fun _ _ => True.intro)
  samples_on_band := by
    intro j p hp
    exact linear_sample_bound w s p hp.2

-- Modern dependency score: 3/18 (M=3, H=15; transitive project theorems/axioms).
theorem harmonic_endpoint_eq (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (j : Nat) :
    GeneralForceEndpoint.endpoint (harmonicOracle w hw) E0 T hE s j = HarmonicDyadic.endpoint w T s j := by
  rw [GeneralForceEndpoint.endpoint,harmonic_field,run_eq_schedule]
  rfl

-- Modern dependency score: 119/277 (M=119, H=158; transitive project theorems/axioms).
theorem harmonic_name_equiv (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    CauchyValues.NameEquiv
      (GeneralForceEndpoint.endpointName (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
        (harmonicBound w s) s hE (conditions w E0 T s hw hE hT hs))
      (HarmonicDyadic.endpointName w T s hT hs) := by
  intro eps heps
  refine ⟨0,fun j _ => ?_⟩
  change Fraction.lt (CauchyValues.distance (GeneralForceEndpoint.endpoint (harmonicOracle w hw) E0 T hE s j)
    (HarmonicDyadic.endpoint w T s j)) eps
  rw [harmonic_endpoint_eq]
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (FiniteEstimates.stateDistance_self_zero _))
    ((Fraction.positive_iff_zero_lt eps).mp heps)

-- Modern dependency score: 127/287 (M=127, H=160; transitive project theorems/axioms).
theorem harmonic_value_eq (w E0 T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hE : 0 < E0.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    GeneralForceEndpoint.endpointValue (harmonicOracle w hw) E0 T (Fraction.ofInt 1) w.abs
      (harmonicBound w s) s hE (conditions w E0 T s hw hE hT hs) =
      CauchyValues.realize (HarmonicDyadic.endpointName w T s hT hs) :=
  Quotient.sound (harmonic_name_equiv w E0 T s hw hE hT hs)

end NewtonLimitDynamics.Polygon.HarmonicGeneralEndpoint
