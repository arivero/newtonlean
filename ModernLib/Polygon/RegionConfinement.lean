import ModernLib.Polygon.GeneralForcePrecision
import BarrowLib.Polygon.CalibratedRefinement
import BarrowLib.Polygon.TriangleBounds

/-! Finite regional confinement before force sampling. One partial-time
invariant controls actual runs and restarted shadow cells. The only force
bound is on the named region; no whole-plane regularity, supplied motion or
completed quantity is used. Kepler sampling and localization of the existing
completion are separate remaining parts of handoff A.6. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceEndpoint
open NewtonLimitDynamics TimeSubdivision PointBounds HarmonicDyadic

def velocityCap (T B : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (pointNorm s.2) (Fraction.mul T B)

-- Modern dependency score: 0/4 (M=0, H=4; transitive project theorems/axioms).
theorem velocityCap_nonnegative (T B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hB : 0 ≤ B.num) : 0 ≤ (velocityCap T B s).num :=
  Fraction.nonnegative_add _ _ (pointNorm_nonnegative _)
    (Fraction.nonnegative_mul _ _ hT hB)

-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
theorem duration_le_window (T : Fraction) (hT : 0 ≤ T.num) (j : Nat) :
    Fraction.le (duration T j) T := by
  have hp : (1 : Int) ≤ (2 : Int)^j := by
    have hj := two_pow_ge_succ j
    have hn : (0 : Int) ≤ (j : Int) := Int.ofNat_nonneg j
    omega
  have hm := Int.mul_le_mul_of_nonneg_left hp
    (Int.mul_nonneg hT (Int.le_of_lt T.den_pos))
  simpa only [duration,Fraction.le,Int.mul_one,Int.mul_assoc] using hm

-- Modern dependency score: 0/2 (M=0, H=2; transitive project theorems/axioms).
theorem fine_time (T : Fraction) (j : Nat) :
    Fraction.equiv
      (BoundedIteration.time (duration T (j+1)) (2*blocks j)) T := by
  have hn : 2*blocks j = blocks (j+1) := by rw [blocks_succ]; omega
  rw [hn]
  exact blocks_duration T (j+1)

-- Modern dependency score: 0/10 (M=0, H=10; transitive project theorems/axioms).
theorem coarse_time (T : Fraction) (j : Nat) :
    Fraction.equiv
      (BoundedIteration.time
        (Fraction.add (duration T (j+1)) (duration T (j+1))) (blocks j)) T :=
  Fraction.equiv_trans
    (Fraction.mul_equiv (Fraction.equiv_refl _) (Fraction.equiv_symm (duration_halving T j)))
    (blocks_duration T j)

end NewtonLimitDynamics.Polygon.GeneralForceEndpoint

namespace NewtonLimitDynamics.Polygon.RegionConfinement
open NewtonLimitDynamics TimeSubdivision PointBounds ForceClasses
open GeneralForceEndpoint

def Band (r R : Fraction) (p : Point) : Prop :=
  Fraction.le r (pointNorm p) ∧ Fraction.le (pointNorm p) R

/-- Geometric and small-time data, without a confinement field. For a ball,
choose r=0; an annulus uses the conserved areal product and positive speed. -/
structure Frame (region : Point → Prop) (T B r R : Fraction) (s0 : Point × Point) where
  time_nonnegative : 0 ≤ T.num
  bound_nonnegative : 0 ≤ B.num
  inner_zero_or_speed_positive : r.num = 0 ∨ 0 < (velocityCap T B s0).num
  areal_bound : Fraction.le (Fraction.mul r (velocityCap T B s0)) (CentralSchedule.momentum s0).abs
  outer_bound : Fraction.le
    (Fraction.add (pointNorm s0.1) (Fraction.mul T (velocityCap T B s0))) R
  contains_band : ∀ p, Band r R p → region p

structure Invariant (T B : Fraction) (s0 : Point × Point) (t : Fraction) (q : Point × Point) where
  velocity_bound : Fraction.le (pointNorm q.2)
    (Fraction.add (pointNorm s0.2) (Fraction.mul t B))
  position_bound : Fraction.le (pointNorm q.1)
    (Fraction.add (pointNorm s0.1) (Fraction.mul t (velocityCap T B s0)))
  areal_product : Fraction.equiv (CentralSchedule.momentum q) (CentralSchedule.momentum s0)

/-- The regular ball case permits zero areal product and zero speed. -/
def ball_frame (region : Point → Prop) (T B R : Fraction) (s0 : Point × Point)
    (hT : 0 ≤ T.num) (hB : 0 ≤ B.num)
    (ho : Fraction.le (Fraction.add (pointNorm s0.1) (Fraction.mul T (velocityCap T B s0))) R)
    (hR : ∀ p, Fraction.le (pointNorm p) R → region p) :
    Frame region T B (Fraction.ofInt 0) R s0 where
  time_nonnegative := hT
  bound_nonnegative := hB
  inner_zero_or_speed_positive := Or.inl rfl
  outer_bound := ho
  contains_band := fun p hp => hR p hp.2
  areal_bound := by
    unfold Fraction.le Fraction.mul Fraction.ofInt
    simp only [Int.zero_mul,Int.one_mul]
    exact Int.mul_nonneg (Fraction.abs_num_nonnegative _) (Int.le_of_lt (velocityCap T B s0).den_pos)

-- Modern dependency score: 0/3 (M=0, H=3; transitive project theorems/axioms).
theorem initial_invariant (T B : Fraction) (s0 : Point × Point) :
    Invariant T B s0 (Fraction.ofInt 0) s0 := by
  refine ⟨?_,?_,Fraction.equiv_refl _⟩ <;> apply Fraction.le_of_equiv <;>
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.add_zero] <;> ac_nf

/-- Determinant conservation supplies the lower radius; no division by a
possibly zero speed is made in the ball case. -/
-- Modern dependency score: 0/28 (M=0, H=28; transitive project theorems/axioms).
theorem band_of_bounds (region : Point → Prop) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame region T B r R s0)
    (p v : Point) (hp : Fraction.le (pointNorm p) R)
    (hv : Fraction.le (pointNorm v) (velocityCap T B s0))
    (hm : Fraction.equiv (det p v) (CentralSchedule.momentum s0)) : Band r R p := by
  refine ⟨?_,hp⟩
  rcases d.inner_zero_or_speed_positive with hz | hV
  · unfold Fraction.le
    simp only [hz,Int.zero_mul]
    exact Int.mul_nonneg (pointNorm_nonnegative p) (Int.le_of_lt r.den_pos)
  · exact TriangleBounds.radius_lower_of_areal_bound p v r _ hV hv
      (Fraction.le_equiv_right d.areal_bound (Fraction.equiv_symm (Fraction.abs_equiv hm)))

-- Modern dependency score: 2/32 (M=2, H=30; transitive project theorems/axioms).
theorem invariant_band (region : Point → Prop) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame region T B r R s0)
    (t : Fraction) (q : Point × Point) (ht : Fraction.le t T)
    (hq : Invariant T B s0 t q) : Band r R q.1 := by
  have hp := Fraction.magnitudes.le_trans hq.position_bound
    (Fraction.add_le_add_left
      (Fraction.mul_le_mul_nonnegative ht (velocityCap T B s0)
        (velocityCap_nonnegative T B s0 d.time_nonnegative d.bound_nonnegative)) _)
  have hv := Fraction.magnitudes.le_trans hq.velocity_bound
    (Fraction.add_le_add_left (Fraction.mul_le_mul_nonnegative ht B d.bound_nonnegative) _)
  exact band_of_bounds region T B r R s0 d q.1 q.2
    (Fraction.magnitudes.le_trans hp d.outer_bound) hv hq.areal_product

/-- The drift arrives inside the region before its force value is evaluated. -/
-- Modern dependency score: 2/41 (M=2, H=39; transitive project theorems/axioms).
theorem arrival_band (region : Point → Prop) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame region T B r R s0)
    (a : Point → Point) (t h : Fraction) (q : Point × Point)
    (hh : 0 ≤ h.num) (ht : Fraction.le (Fraction.add t h) T)
    (hq : Invariant T B s0 t q) : Band r R (FiniteEstimates.cell a h q).1 := by
  have hprior := Fraction.magnitudes.le_trans (Fraction.le_add_nonnegative t h hh) ht
  have hv := Fraction.magnitudes.le_trans hq.velocity_bound
    (Fraction.add_le_add_left (Fraction.mul_le_mul_nonnegative hprior B d.bound_nonnegative) _)
  have hpos := Fraction.le_equiv_right (FiniteEstimates.cell_position_growth a h q)
    (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.mul_equiv
      (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl _)))
  have hp := Fraction.magnitudes.le_trans hpos
    (Fraction.add_le_add hq.position_bound (Fraction.mul_le_mul_nonnegative_left hv h hh))
  have he : Fraction.equiv
      (Fraction.add (Fraction.add (pointNorm s0.1) (Fraction.mul t (velocityCap T B s0)))
        (Fraction.mul h (velocityCap T B s0)))
      (Fraction.add (pointNorm s0.1) (Fraction.mul (Fraction.add t h) (velocityCap T B s0))) := by
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
    ac_nf
  have hp' := Fraction.magnitudes.le_trans (Fraction.le_equiv_right hp he)
    (Fraction.add_le_add_left
      (Fraction.mul_le_mul_nonnegative ht (velocityCap T B s0)
        (velocityCap_nonnegative T B s0 d.time_nonnegative d.bound_nonnegative)) _)
  have hm := Fraction.equiv_trans (CentralSchedule.det_drift q.1 q.2 h) hq.areal_product
  exact band_of_bounds region T B r R s0 d _ q.2
    (Fraction.magnitudes.le_trans hp' d.outer_bound) hv hm

/-- One invariant step. The region bound is used only after arrival_band. -/
-- Modern dependency score: 3/49 (M=3, H=46; transitive project theorems/axioms).
theorem advance (region : Point → Prop) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame region T B r R s0)
    (a : Point → Point) (hc : CentralSchedule.central a)
    (hb : ∀ p, Band r R p → Fraction.le (pointNorm (a p)) B)
    (t h : Fraction) (q : Point × Point) (hh : 0 ≤ h.num)
    (ht : Fraction.le (Fraction.add t h) T) (hq : Invariant T B s0 t q) :
    Invariant T B s0 (Fraction.add t h) (FiniteEstimates.cell a h q) := by
  have ha := hb _ (arrival_band region T B r R s0 d a t h q hh ht hq)
  have hv := Fraction.le_equiv_right (FiniteEstimates.cell_velocity_growth a h B q ha)
    (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.mul_equiv
      (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl _)))
  have hv' := Fraction.magnitudes.le_trans hv
    (Fraction.add_le_add_right hq.velocity_bound (Fraction.mul h B))
  have hvq : Fraction.le (pointNorm q.2) (velocityCap T B s0) :=
    Fraction.magnitudes.le_trans hq.velocity_bound
    (Fraction.add_le_add_left (Fraction.mul_le_mul_nonnegative
      (Fraction.magnitudes.le_trans (Fraction.le_add_nonnegative t h hh) ht)
      B d.bound_nonnegative) _)
  have hp := Fraction.le_equiv_right (FiniteEstimates.cell_position_growth a h q)
    (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.mul_equiv
      (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl _)))
  have hp' := Fraction.magnitudes.le_trans hp
    (Fraction.add_le_add hq.position_bound (Fraction.mul_le_mul_nonnegative_left hvq h hh))
  refine ⟨?_,?_,Fraction.equiv_trans (CentralSchedule.cell_momentum a hc h q) hq.areal_product⟩
  · apply Fraction.le_equiv_right hv'
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
    ac_nf
  · apply Fraction.le_equiv_right hp'
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
    ac_nf

/-- All finite mesh levels inherit the regional bound without BoundedSamples
as an input. The force need not be continuous for this confinement result. -/
-- Modern dependency score: 5/52 (M=5, H=47; transitive project theorems/axioms).
theorem run_invariant (region : Point → Prop) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame region T B r R s0)
    (a : Point → Point) (hc : CentralSchedule.central a)
    (hb : ∀ p, Band r R p → Fraction.le (pointNorm (a p)) B)
    (h : Fraction) (hh : 0 ≤ h.num) :
    (n : Nat) → Fraction.le (BoundedIteration.time h n) T →
    Invariant T B s0 (BoundedIteration.time h n) (BoundedIteration.run a h s0 n)
  | 0, _ => by
      have hi := initial_invariant T B s0
      have he : Fraction.equiv (Fraction.ofInt 0) (BoundedIteration.time h 0) := by
        simp only [BoundedIteration.time,Fraction.equiv,Fraction.ofInt,Fraction.mul,
          Int.natCast_zero,Int.zero_mul,Int.mul_zero]
      exact ⟨Fraction.le_equiv_right hi.velocity_bound
          (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.mul_equiv he (Fraction.equiv_refl _))),
        Fraction.le_equiv_right hi.position_bound
          (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.mul_equiv he (Fraction.equiv_refl _))),
        hi.areal_product⟩
  | n+1, ht => by
      have he : Fraction.equiv (Fraction.add (BoundedIteration.time h n) h)
          (BoundedIteration.time h (n+1)) := by
        simp only [BoundedIteration.time,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
          Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
        ac_nf
      have hi := run_invariant region T B r R s0 d a hc hb h hh n
        (Fraction.magnitudes.le_trans (BoundedIteration.time_monotone h hh n (n+1) (by omega)) ht)
      have hs := advance region T B r R s0 d a hc hb _ h _ hh
        (Fraction.le_equiv_left he ht) hi
      refine ⟨?_,?_,hs.areal_product⟩
      · exact Fraction.le_equiv_right hs.velocity_bound
          (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.mul_equiv he (Fraction.equiv_refl _)))
      · exact Fraction.le_equiv_right hs.position_bound
          (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.mul_equiv he (Fraction.equiv_refl _)))

-- Modern dependency score: 7/54 (M=7, H=47; transitive project theorems/axioms).
theorem run_band (region : Point → Prop) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame region T B r R s0)
    (a : Point → Point) (hc : CentralSchedule.central a)
    (hb : ∀ p, Band r R p → Fraction.le (pointNorm (a p)) B)
    (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) T) :
    Band r R (BoundedIteration.run a h s0 n).1 :=
  invariant_band region T B r R s0 d _ _ hn
    (run_invariant region T B r R s0 d a hc hb h hh n hn)

/-- Bounds at every actual sample are a conclusion of confinement, never
the induction hypothesis used to establish it. -/
-- Modern dependency score: 8/55 (M=8, H=47; transitive project theorems/axioms).
theorem run_bounded_samples (region : Point → Prop) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame region T B r R s0)
    (a : Point → Point) (hc : CentralSchedule.central a)
    (hb : ∀ p, Band r R p → Fraction.le (pointNorm (a p)) B)
    (h : Fraction) (hh : 0 ≤ h.num) (n : Nat)
    (hn : Fraction.le (BoundedIteration.time h n) T) :
    BoundedIteration.BoundedSamples a h s0 B n := by
  intro i hi
  exact hb _ (run_band region T B r R s0 d a hc hb h hh (i+1)
    (Fraction.magnitudes.le_trans (BoundedIteration.time_monotone h hh (i+1) n (by omega)) hn))

/-- Both coarse-field shadow arrivals are confined. Their partial-time speed
budgets account for the first shadow kick before the second arrival. -/
-- Modern dependency score: 8/58 (M=8, H=50; transitive project theorems/axioms).
theorem shadow_bands (region : Point → Prop) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame region T B r R s0)
    (a : Point → Point) (hc : CentralSchedule.central a)
    (hb : ∀ p, Band r R p → Fraction.le (pointNorm (a p)) B)
    (m k : Nat) (hk : k < HarmonicDyadic.blocks m) :
    Band r R (FiniteEstimates.cell a (HarmonicDyadic.duration T (m+1))
      (FiniteAccumulation.coarseAt a (HarmonicDyadic.duration T (m+1)) s0 k)).1 ∧
    Band r R (FiniteEstimates.twoHalf a (HarmonicDyadic.duration T (m+1))
      (FiniteAccumulation.coarseAt a (HarmonicDyadic.duration T (m+1)) s0 k)).1 := by
  let h := HarmonicDyadic.duration T (m+1)
  let t := BoundedIteration.time (Fraction.add h h) k
  let q := FiniteAccumulation.coarseAt a h s0 k
  have hh : 0 ≤ h.num := d.time_nonnegative
  have hfull : 0 ≤ (Fraction.add h h).num := Fraction.nonnegative_add _ _ hh hh
  have hend := Fraction.magnitudes.le_trans
    (BoundedIteration.time_monotone (Fraction.add h h) hfull (k+1)
      (HarmonicDyadic.blocks m) (by omega)) (Fraction.le_of_equiv (coarse_time T m))
  have he : Fraction.equiv (Fraction.add (Fraction.add t h) h)
      (BoundedIteration.time (Fraction.add h h) (k+1)) := by
    simp only [t,BoundedIteration.time,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  have hsecond := Fraction.le_equiv_left he hend
  have hfirst := Fraction.magnitudes.le_trans (Fraction.le_add_nonnegative (Fraction.add t h) h hh) hsecond
  have hprior := Fraction.magnitudes.le_trans (Fraction.le_add_nonnegative t h hh) hfirst
  have hq : Invariant T B s0 t q := by
    dsimp only [q,t]
    rw [CalibratedRefinement.coarseAt_eq_run]
    exact run_invariant region T B r R s0 d a hc hb (Fraction.add h h) hfull k hprior
  have h1 := advance region T B r R s0 d a hc hb t h q hh hfirst hq
  have h2 := advance region T B r R s0 d a hc hb (Fraction.add t h) h
    (FiniteEstimates.cell a h q) hh hsecond h1
  exact ⟨invariant_band region T B r R s0 d _ _ hfirst h1,
    invariant_band region T B r R s0 d _ _ hsecond h2⟩

/-- Regional one-cell comparison: certify both drift arrivals first, then
use local Lipschitz comparison and the calibrated pointwise primitive. -/
-- Modern dependency score: 6/58 (M=6, H=52; transitive project theorems/axioms).
theorem sampled_cell_comparison (o : CentralOracle) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame o.region T B r R s0)
    (L tau : Fraction) (hL : LipschitzOn o.toOracle L) (htau : 0 < tau.num)
    (i j : Nat) (hij : i ≤ j) (t u h : Fraction) (q z : Point × Point)
    (hh : 0 ≤ h.num) (ht : Fraction.le (Fraction.add t h) T)
    (hu : Fraction.le (Fraction.add u h) T)
    (hq : Invariant T B s0 t q) (hz : Invariant T B s0 u z) :
    Fraction.le (TimeCalibration.distance tau
      (FiniteEstimates.cell (o.sample i) h q) (FiniteEstimates.cell (o.sample j) h z))
      (Fraction.add
        (Fraction.mul (TimeCalibration.amplification tau h L htau)
          (TimeCalibration.distance tau q z))
        (Fraction.mul (Fraction.mul tau h.abs)
          (Fraction.add (Fraction.add (o.error i) (o.error i)) (o.error i)))) := by
  have hp := d.contains_band _ (arrival_band o.region T B r R s0 d
    (o.sample i) t h q hh ht hq)
  have hr := d.contains_band _ (arrival_band o.region T B r R s0 d
    (o.sample j) u h z hh hu hz)
  exact TimeCalibration.cell_amplification_at tau htau (o.sample i) (o.sample j)
    h L _ q z hL.1 (samples_comparison_contract o.toOracle L hL i j hij _ _ hp hr)

/-- Actual paired refinement on a certified band. Both fine arrivals, both
coarse-field shadow arrivals and the full coarse arrival are certified before
any of the four local force comparisons is used. -/
-- Modern dependency score: 17/129 (M=17, H=112; transitive project theorems/axioms).
theorem sampled_refinement_bound (o : CentralOracle) (T B r R : Fraction)
    (s0 : Point × Point) (d : Frame o.region T B r R s0)
    (L tau : Fraction) (hL : LipschitzOn o.toOracle L) (htau : 0 < tau.num)
    (i j : Nat) (hij : i ≤ j)
    (hbi : ∀ p, Band r R p → Fraction.le (pointNorm (o.sample i p)) B)
    (hbj : ∀ p, Band r R p → Fraction.le (pointNorm (o.sample j p)) B) (m n : Nat) (hn : n ≤ HarmonicDyadic.blocks m)
    (hs : TimeCalibration.Window tau (HarmonicDyadic.duration T (m+1)) L htau (2*n)) :
    Fraction.le (TimeCalibration.distance tau
      (FiniteAccumulation.fineAt (o.sample j) (HarmonicDyadic.duration T (m+1)) s0 n)
      (FiniteAccumulation.coarseAt (o.sample i) (HarmonicDyadic.duration T (m+1)) s0 n))
      (Fraction.mul (Fraction.ofInt (2*(n : Int)))
        (CalibratedRefinement.blockSource tau (HarmonicDyadic.duration T (m+1)) L
          (Fraction.add (Fraction.add (o.error i) (o.error i)) (o.error i))
          B (velocityCap T B s0) htau)) := by
  let h := HarmonicDyadic.duration T (m+1)
  let E := Fraction.add (Fraction.add (o.error i) (o.error i)) (o.error i)
  have hh : 0 ≤ h.num := d.time_nonnegative
  have hfull : 0 ≤ (Fraction.add h h).num := Fraction.nonnegative_add _ _ hh hh
  have hf : ∀ k, k ≤ 2*HarmonicDyadic.blocks m →
      Band r R (BoundedIteration.run (o.sample j) h s0 k).1 := by
    intro k hk
    exact run_band o.region T B r R s0 d _ (sample_central o j) hbj h hh k
      (Fraction.magnitudes.le_trans
        (BoundedIteration.time_monotone h hh k (2*HarmonicDyadic.blocks m) hk)
        (Fraction.le_of_equiv (fine_time T m)))
  have hct : ∀ k, k ≤ HarmonicDyadic.blocks m →
      Fraction.le (BoundedIteration.time (Fraction.add h h) k) T := by
    intro k hk
    exact Fraction.magnitudes.le_trans
      (BoundedIteration.time_monotone _ hfull k (HarmonicDyadic.blocks m) hk)
      (Fraction.le_of_equiv (coarse_time T m))
  have hc : ∀ k, k ≤ HarmonicDyadic.blocks m →
      Band r R (BoundedIteration.run (o.sample i) (Fraction.add h h) s0 k).1 := by
    intro k hk
    exact run_band o.region T B r R s0 d _ (sample_central o i) hbi
      _ hfull k (hct k hk)
  have hcross : ∀ p q, o.region p → o.region q →
      Fraction.le (FiniteEstimates.pointDistance (o.sample j p) (o.sample i q))
        (Fraction.add (Fraction.mul L (FiniteEstimates.pointDistance p q)) E) := by
    intro p q hp hq
    have he := samples_comparison_contract o.toOracle L hL i j hij q p hq hp
    exact Fraction.le_equiv_right
      (Fraction.le_equiv_left (FiniteEstimates.pointDistance_symm _ _) he)
      (Fraction.add_equiv
        (Fraction.mul_equiv_left L (FiniteEstimates.pointDistance_symm _ _))
        (Fraction.equiv_refl _))
  apply CalibratedRefinement.actual_uniform_error_at tau htau (o.sample j) (o.sample i)
    h L E B (velocityCap T B s0) s0 hL.1
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_add _ _ (o.error_nonnegative i) (o.error_nonnegative i))
      (o.error_nonnegative i)) d.bound_nonnegative
    (velocityCap_nonnegative T B s0 d.time_nonnegative d.bound_nonnegative) n hs
  · intro k hk
    have hkm : k < HarmonicDyadic.blocks m := by omega
    obtain ⟨hb1,hb2⟩ := shadow_bands o.region T B r R s0 d _
      (sample_central o i) hbi m k hkm
    have ha1 : Band r R (FiniteEstimates.cell (o.sample j) h
        (FiniteAccumulation.fineAt (o.sample j) h s0 k)).1 := by
      simpa only [CalibratedRefinement.fineAt_eq_run,BoundedIteration.run] using
        hf (2*k+1) (by omega)
    have ha2 : Band r R (FiniteEstimates.twoHalf (o.sample j) h
        (FiniteAccumulation.fineAt (o.sample j) h s0 k)).1 := by
      simpa only [CalibratedRefinement.fineAt_eq_run,FiniteEstimates.twoHalf,
        BoundedIteration.run] using hf (2*k+2) (by omega)
    have hc1 : Band r R (FiniteEstimates.oneFull (o.sample i) h
        (FiniteAccumulation.coarseAt (o.sample i) h s0 k)).1 := by
      simpa only [CalibratedRefinement.coarseAt_eq_run,FiniteEstimates.oneFull,
        BoundedIteration.run] using hc (k+1) (by omega)
    exact ⟨hcross _ _ (d.contains_band _ ha1) (d.contains_band _ hb1),
      hcross _ _ (d.contains_band _ ha2) (d.contains_band _ hb2),
      samples_comparison_contract o.toOracle L hL i i (Nat.le_refl _) _ _
        (d.contains_band _ hb1) (d.contains_band _ hc1),
      samples_comparison_contract o.toOracle L hL i i (Nat.le_refl _) _ _
        (d.contains_band _ hb2) (d.contains_band _ hc1)⟩
  · intro k hk
    exact hbi _ (shadow_bands o.region T B r R s0 d _
      (sample_central o i) hbi m k (by omega)).1
  · intro k hk
    have hv := (run_invariant o.region T B r R s0 d _ (sample_central o i) hbi
      (Fraction.add h h) hfull k (hct k (by omega))).velocity_bound
    simpa only [CalibratedRefinement.coarseAt_eq_run] using!
      Fraction.magnitudes.le_trans hv (Fraction.add_le_add_left
        (Fraction.mul_le_mul_nonnegative (hct k (by omega)) B d.bound_nonnegative) _)

/-- Equivalent represented durations retain their own actual force samples.
Membership of both arrival families is derived from the same regional frame. -/
-- Modern dependency score: 14/112 (M=14, H=98; transitive project theorems/axioms).
theorem sampled_equivalent_duration_bound (o : CentralOracle) (T B r R : Fraction)
    (s0 : Point × Point) (f : Frame o.region T B r R s0)
    (L tau : Fraction) (hL : LipschitzOn o.toOracle L) (htau : 0 < tau.num)
    (i j : Nat) (hij : i ≤ j)
    (hbi : ∀ p, Band r R p → Fraction.le (pointNorm (o.sample i p)) B)
    (hbj : ∀ p, Band r R p → Fraction.le (pointNorm (o.sample j p)) B) (d e : Fraction) (hde : Fraction.equiv d e)
    (hd : 0 ≤ d.num) (he : 0 ≤ e.num) (n : Nat)
    (hdt : Fraction.le (BoundedIteration.time d n) T)
    (het : Fraction.le (BoundedIteration.time e n) T)
    (hs : TimeCalibration.Window tau d L htau n) :
    Fraction.le (TimeCalibration.distance tau
      (BoundedIteration.run (o.sample i) d s0 n) (BoundedIteration.run (o.sample j) e s0 n))
      (Fraction.mul (Fraction.ofInt (2*(n : Int)))
        (Fraction.mul (Fraction.mul tau d.abs)
          (Fraction.add (Fraction.add (o.error i) (o.error i)) (o.error i)))) := by
  apply EquivalentDuration.run_uniform_error_at tau htau (o.sample i) (o.sample j)
    d e L _ s0 hde hL.1
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_add _ _ (o.error_nonnegative i) (o.error_nonnegative i))
      (o.error_nonnegative i)) n hs
  intro k hk
  have hp := run_band o.region T B r R s0 f _ (sample_central o i) hbi d hd (k+1)
    (Fraction.magnitudes.le_trans (BoundedIteration.time_monotone d hd (k+1) n (by omega)) hdt)
  have hq := run_band o.region T B r R s0 f _ (sample_central o j) hbj e he (k+1)
    (Fraction.magnitudes.le_trans (BoundedIteration.time_monotone e he (k+1) n (by omega)) het)
  exact samples_comparison_contract o.toOracle L hL i j hij _ _
    (f.contains_band _ hp) (f.contains_band _ hq)

end NewtonLimitDynamics.Polygon.RegionConfinement
