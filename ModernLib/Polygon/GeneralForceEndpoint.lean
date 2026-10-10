import ModernLib.Polygon.GeneralForcePrecision
import BarrowLib.Polygon.CalibratedRefinement
import ModernLib.Polygon.RegionConfinement

/-! Construct fixed-time motion values from actual sampled central polygons.
Lipschitz comparison and sample bounds hold only on a certified band. The
partial-time invariant derives actual/coarse and both shadow membership
before force sampling; no whole-plane or supplied confinement trace is used. No motion-Cauchy,
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
  calibration_positive : 0 < tau.num
  lipschitz : LipschitzOn o.toOracle L
  window : Fraction.le
    (Fraction.mul T (TimeCalibration.rate tau L calibration_positive)) ⟨1,2,by decide⟩
  inner_radius : Fraction
  outer_radius : Fraction
  frame : RegionConfinement.Frame o.region T B inner_radius outer_radius s
  samples_on_band : ∀ j p, RegionConfinement.Band inner_radius outer_radius p →
    Fraction.le (pointNorm (field o E0 hE j p)) B

namespace Conditions
variable {o : CentralOracle} {E0 T tau L B : Fraction} {s : Point × Point} {hE : 0 < E0.num}

def time_nonnegative (d : Conditions o E0 T tau L B s hE) : 0 ≤ T.num :=
  d.frame.time_nonnegative

def bound_nonnegative (d : Conditions o E0 T tau L B s hE) : 0 ≤ B.num :=
  d.frame.bound_nonnegative

-- Modern dependency score: 12/60 (M=12, H=48; transitive project theorems/axioms).
theorem run_band (d : Conditions o E0 T tau L B s hE)
    (j : Nat) (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) T) :
    RegionConfinement.Band d.inner_radius d.outer_radius
      (BoundedIteration.run (field o E0 hE j) h s n).1 :=
  RegionConfinement.run_band o.region T B _ _ s d.frame _
    (sample_central o _) (d.samples_on_band j) h hh n hn

-- Modern dependency score: 13/61 (M=13, H=48; transitive project theorems/axioms).
theorem run_region (d : Conditions o E0 T tau L B s hE)
    (j : Nat) (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) T) :
    o.region (BoundedIteration.run (field o E0 hE j) h s n).1 :=
  d.frame.contains_band _ (d.run_band j h hh n hn)

-- Modern dependency score: 13/62 (M=13, H=49; transitive project theorems/axioms).
theorem actual_samples (d : Conditions o E0 T tau L B s hE) (j : Nat) :
    BoundedIteration.BoundedSamples (field o E0 hE j) (duration T j) s B (blocks j) :=
  RegionConfinement.run_bounded_samples o.region T B _ _ s d.frame _
    (sample_central o _) (d.samples_on_band j) (duration T j) d.time_nonnegative (blocks j)
    (Fraction.le_of_equiv (blocks_duration T j))

-- Modern dependency score: 14/64 (M=14, H=50; transitive project theorems/axioms).
theorem coarse_samples (d : Conditions o E0 T tau L B s hE) (j : Nat) :
    BoundedIteration.BoundedSamples (field o E0 hE j)
      (Fraction.add (duration T (j+1)) (duration T (j+1))) s B (blocks j) :=
  RegionConfinement.run_bounded_samples o.region T B _ _ s d.frame _
    (sample_central o _) (d.samples_on_band j)
    (Fraction.add (duration T (j+1)) (duration T (j+1)))
    (Fraction.nonnegative_add _ _ d.time_nonnegative d.time_nonnegative) (blocks j)
    (Fraction.le_of_equiv (coarse_time T j))

-- Modern dependency score: 13/64 (M=13, H=51; transitive project theorems/axioms).
theorem shadow_samples (d : Conditions o E0 T tau L B s hE)
    (j k : Nat) (hk : k < blocks j) : Fraction.le
    (pointNorm (field o E0 hE j
      (FiniteEstimates.cell (field o E0 hE j) (duration T (j+1))
        (FiniteAccumulation.coarseAt (field o E0 hE j) (duration T (j+1)) s k)).1)) B :=
  d.samples_on_band j _ (RegionConfinement.shadow_bands o.region T B _ _ s d.frame _
    (sample_central o _) (d.samples_on_band j) j k hk).1

end Conditions

noncomputable def sampleError (o : CentralOracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) : Fraction :=
  let e := o.error (precision o.toOracle E0 hE j)
  Fraction.add (Fraction.add e e) e

-- Modern dependency score: 1/2 (M=1, H=1; transitive project theorems/axioms).
theorem sampleError_nonnegative (o : CentralOracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) : 0 ≤ (sampleError o E0 hE j).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_add _ _ (o.error_nonnegative _) (o.error_nonnegative _))
    (o.error_nonnegative _)

-- Modern dependency score: 5/34 (M=5, H=29; transitive project theorems/axioms).
theorem cross_contract (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) (p q : Point) (hp : o.region p) (hq : o.region q) :
    Fraction.le (FiniteEstimates.pointDistance (field o E0 hE (j+1) p) (field o E0 hE j q))
      (Fraction.add (Fraction.mul L (FiniteEstimates.pointDistance p q)) (sampleError o E0 hE j)) := by
  have hc := samples_comparison_contract o.toOracle L d.lipschitz
    (precision o.toOracle E0 hE j) (precision o.toOracle E0 hE (j+1))
    (precision_successor o.toOracle E0 hE j) q p hq hp
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_left (FiniteEstimates.pointDistance_symm _ _) hc)
    (Fraction.add_equiv (Fraction.mul_equiv_left L (FiniteEstimates.pointDistance_symm _ _))
      (Fraction.equiv_refl _))

-- Modern dependency score: 4/28 (M=4, H=24; transitive project theorems/axioms).
theorem local_contract (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) (p q : Point) (hp : o.region p) (hq : o.region q) :
    Fraction.le (FiniteEstimates.pointDistance (field o E0 hE j p) (field o E0 hE j q))
      (Fraction.add (Fraction.mul L (FiniteEstimates.pointDistance p q)) (sampleError o E0 hE j)) :=
  samples_comparison_contract o.toOracle L d.lipschitz _ _ (Nat.le_refl _) p q hp hq

-- Modern dependency score: 15/68 (M=15, H=53; transitive project theorems/axioms).
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

-- Modern dependency score: 1/23 (M=1, H=22; transitive project theorems/axioms).
theorem fine_window (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    TimeCalibration.Window tau (duration T (j+1)) L d.calibration_positive (2*blocks j) := by
  have ht := Fraction.equiv_trans
    (Fraction.mul_equiv (Fraction.equiv_refl _)
      (Fraction.abs_of_nonnegative (duration T (j+1)) d.time_nonnegative)) (fine_time T j)
  exact TimeCalibration.window_of_elapsed _ _ T _ d.calibration_positive d.lipschitz.1 _
    (Fraction.le_of_equiv ht) d.window

-- Modern dependency score: 1/23 (M=1, H=22; transitive project theorems/axioms).
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

/-- Actual prefix comparison with a full-window budget, including representation error. -/
-- Modern dependency score: 24/151 (M=24, H=127; transitive project theorems/axioms).
theorem paired_finite_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j n : Nat) (hn : n ≤ blocks j) :
    Fraction.le (TimeCalibration.distance tau
      (BoundedIteration.run (field o E0 hE (j+1)) (duration T (j+1)) s (2*n))
      (BoundedIteration.run (field o E0 hE j) (duration T j) s n))
      (Fraction.add
        (Fraction.mul (Fraction.ofInt (2*(blocks j : Int)))
          (CalibratedRefinement.blockSource tau (duration T (j+1)) L
            (sampleError o E0 hE j) B (velocityCap T B s) d.calibration_positive))
        (Fraction.mul (Fraction.ofInt (2*(blocks j : Int)))
          (Fraction.mul
            (Fraction.mul tau
              (Fraction.add (duration T (j+1)) (duration T (j+1))).abs)
            (sampleError o E0 hE j)))) := by
  have h1 := RegionConfinement.sampled_refinement_bound o T B d.inner_radius d.outer_radius
    s d.frame L tau d.lipschitz d.calibration_positive
    (precision o.toOracle E0 hE j) (precision o.toOracle E0 hE (j+1))
    (precision_successor o.toOracle E0 hE j) (d.samples_on_band j) (d.samples_on_band (j+1))
    j n hn (TimeCalibration.window_mono _ _ _ d.calibration_positive d.lipschitz.1
      (2*n) (2*blocks j) (by omega) (fine_window o E0 T tau L B s hE d j))
  have hfull : 0 ≤ (Fraction.add (duration T (j+1)) (duration T (j+1))).num :=
    Fraction.nonnegative_add _ _ d.time_nonnegative d.time_nonnegative
  have hdtime := Fraction.magnitudes.le_trans
    (BoundedIteration.time_monotone _ hfull n (blocks j) hn)
    (Fraction.le_of_equiv (coarse_time T j))
  have hetime := Fraction.magnitudes.le_trans
    (BoundedIteration.time_monotone (duration T j) d.time_nonnegative n (blocks j) hn)
    (Fraction.le_of_equiv (blocks_duration T j))
  have h2 := RegionConfinement.sampled_equivalent_duration_bound o T B d.inner_radius d.outer_radius
    s d.frame L tau d.lipschitz d.calibration_positive
    (precision o.toOracle E0 hE j) (precision o.toOracle E0 hE j) (Nat.le_refl _)
    (d.samples_on_band j) (d.samples_on_band j)
    (Fraction.add (duration T (j+1)) (duration T (j+1))) (duration T j)
    (Fraction.equiv_symm (duration_halving T j)) hfull d.time_nonnegative n hdtime hetime
    (TimeCalibration.window_mono _ _ _ d.calibration_positive d.lipschitz.1
      n (blocks j) hn (coarse_window o E0 T tau L B s hE d j))
  have htri := TimeCalibration.distance_triangle tau d.calibration_positive
    (FiniteAccumulation.fineAt (field o E0 hE (j+1)) (duration T (j+1)) s n)
    (FiniteAccumulation.coarseAt (field o E0 hE j) (duration T (j+1)) s n)
    (BoundedIteration.run (field o E0 hE j) (duration T j) s n)
  have hb := Fraction.magnitudes.le_trans htri (Fraction.add_le_add h1
    (by simpa only [CalibratedRefinement.coarseAt_eq_run] using! h2))
  rw [CalibratedRefinement.fineAt_eq_run] at hb
  have hc : Fraction.le (Fraction.ofInt (2*(n : Int)))
      (Fraction.ofInt (2*(blocks j : Int))) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one] using
      (show 2*(n : Int) ≤ 2*(blocks j : Int) by omega)
  have hs := CalibratedRefinement.blockSource_nonnegative tau (duration T (j+1)) L
    (sampleError o E0 hE j) B (velocityCap T B s) d.calibration_positive d.lipschitz.1
    (sampleError_nonnegative o E0 hE j) d.bound_nonnegative
    (velocityCap_nonnegative T B s d.time_nonnegative d.bound_nonnegative)
  have he : 0 ≤ (Fraction.mul
      (Fraction.mul tau (Fraction.add (duration T (j+1)) (duration T (j+1))).abs)
      (sampleError o E0 hE j)).num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt d.calibration_positive)
      (Fraction.abs_num_nonnegative _)) (sampleError_nonnegative o E0 hE j)
  exact Fraction.magnitudes.le_trans hb (Fraction.add_le_add
    (Fraction.mul_le_mul_nonnegative hc _ hs) (Fraction.mul_le_mul_nonnegative hc _ he))

-- Modern dependency score: 25/152 (M=25, H=127; transitive project theorems/axioms).
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
  have hb := paired_finite_bound o E0 T tau L B s hE d j (blocks j) (Nat.le_refl _)
  have hn : 2*blocks j = blocks (j+1) := by rw [blocks_succ]; omega
  rw [hn] at hb
  exact hb

/-- The same mesh estimate holds uniformly at every paired prefix. -/
-- Modern dependency score: 26/156 (M=26, H=130; transitive project theorems/axioms).
theorem paired_mesh_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j n : Nat) (hn : n ≤ blocks j) :
    Fraction.le (TimeCalibration.distance tau
      (BoundedIteration.run (field o E0 hE (j+1)) (duration T (j+1)) s (2*n))
      (BoundedIteration.run (field o E0 hE j) (duration T j) s n))
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
  have hb := Fraction.magnitudes.le_trans (paired_finite_bound o E0 T tau L B s hE d j n hn)
    (Fraction.add_le_add_right hm
      (Fraction.mul (Fraction.ofInt (2*(blocks j : Int)))
        (Fraction.mul (Fraction.mul tau (Fraction.add h h).abs) E)))
  rw [Fraction.abs_eq_of_nonnegative h hh, Fraction.abs_eq_of_nonnegative (Fraction.add h h) hfull] at hb
  apply Fraction.le_equiv_right hb
  simp only [h,E,V,blocks,duration,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.natCast_pow,Int.pow_succ,show (7 : Int) = 5+1+1 by rfl,
    Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

-- Modern dependency score: 27/157 (M=27, H=130; transitive project theorems/axioms).
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
  have hb := paired_mesh_bound o E0 T tau L B s hE d j (blocks j) (Nat.le_refl _)
  have hn : 2*blocks j = blocks (j+1) := by rw [blocks_succ]; omega
  rw [hn] at hb
  exact hb

/-- A dimensioned acceleration precision scale remains explicit. -/
def weightedCoefficient (E0 T tau L B : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add
    (Fraction.mul (Fraction.mul T T)
      (CalibratedRefinement.consistencyCoefficient tau T L B (velocityCap T B s)))
    (Fraction.mul (Fraction.ofInt 42) (Fraction.mul (Fraction.mul tau T) E0))

-- Modern dependency score: 1/5 (M=1, H=4; transitive project theorems/axioms).
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
-- Modern dependency score: 30/160 (M=30, H=130; transitive project theorems/axioms).
theorem paired_weighted_tail (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j n : Nat) (hn : n ≤ blocks j) :
    Fraction.le (TimeCalibration.distance tau
      (BoundedIteration.run (field o E0 hE (j+1)) (duration T (j+1)) s (2*n))
      (BoundedIteration.run (field o E0 hE j) (duration T j) s n))
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
  have hb := Fraction.magnitudes.le_trans (paired_mesh_bound o E0 T tau L B s hE d j n hn)
    (Fraction.add_le_add_left hm
      (Fraction.mul (Fraction.mul T (duration T (j+1)))
        (CalibratedRefinement.consistencyCoefficient tau T L B (velocityCap T B s))))
  apply Fraction.le_equiv_right hb
  simp only [weightedCoefficient,GeometricTail.tailCap,duration,Fraction.equiv,
    Fraction.add,Fraction.mul,Fraction.ofInt,Int.pow_succ,
    show (42 : Int) = 7*3*2 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

-- Modern dependency score: 31/161 (M=31, H=130; transitive project theorems/axioms).
theorem adjacent_weighted_tail (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (j : Nat) :
    Fraction.le (TimeCalibration.distance tau
      (endpoint o E0 T hE s (j+1)) (endpoint o E0 T hE s j))
      (GeometricTail.tailCap (weightedCoefficient E0 T tau L B s) (j+1)) := by
  have hb := paired_weighted_tail o E0 T tau L B s hE d j (blocks j) (Nat.le_refl _)
  have hn : 2*blocks j = blocks (j+1) := by rw [blocks_succ]; omega
  rw [hn] at hb
  exact hb

noncomputable def coefficient (E0 T tau L B : Fraction) (s : Point × Point)
    (ht : 0 < tau.num) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) (TimeCalibration.inverse tau ht))
    (weightedCoefficient E0 T tau L B s)

-- Modern dependency score: 2/6 (M=2, H=4; transitive project theorems/axioms).
theorem coefficient_nonnegative (E0 T tau L B : Fraction) (s : Point × Point)
    (hE : 0 < E0.num) (hT : 0 ≤ T.num) (ht : 0 < tau.num)
    (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (coefficient E0 T tau L B s ht).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos))
    (weightedCoefficient_nonnegative E0 T tau L B s hE hT ht hL hB)

-- Modern dependency score: 32/163 (M=32, H=131; transitive project theorems/axioms).
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

-- Modern dependency score: 53/198 (M=53, H=145; transitive project theorems/axioms).
theorem approximants_converge (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (d : Conditions o E0 T tau L B s hE)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ n, N ≤ n → Within (embed (endpoint o E0 T hE s n))
      (endpointValue o E0 T tau L B s hE d) eps :=
  constant_approximants_converge _ eps heps

-- Modern dependency score: 1/8 (M=1, H=7; transitive project theorems/axioms).
theorem zero_time_endpoint (o : CentralOracle) (E0 T : Fraction)
    (hE : 0 < E0.num) (s : Point × Point) (hT : T.num = 0) (j : Nat) :
    stateEquiv (endpoint o E0 T hE s j) s :=
  BoundedIteration.zero_duration_run (field o E0 hE j) (duration T j) hT s (blocks j)

-- Modern dependency score: 47/199 (M=47, H=152; transitive project theorems/axioms).
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
