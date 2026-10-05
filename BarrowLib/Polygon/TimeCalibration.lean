import BarrowLib.Polygon.FiniteEstimates
import BarrowLib.Polygon.ScaledTolerance
import BarrowLib.Polygon.FiniteFactorProducts
import BarrowLib.Polygon.FiniteRecurrence
import BarrowLib.Polygon.BoundedIteration

/-! Calibrated coordinate gauges and finite triangular-map estimates.
A positive rational time calibration is free data. Rescaling the time unit
preserves the weighted gauge, dimensionless growth and sampling budgets.
Cauchy convergence is independent of this choice. This modern elementary
infrastructure assumes no motion, force law, potential or universal scale. -/

namespace NewtonLimitDynamics.Polygon.TimeCalibration
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates

def inverse (tau : Fraction) (ht : 0 < tau.num) : Fraction :=
  ⟨tau.den,tau.num,ht⟩

theorem inverse_positive (tau : Fraction) (ht : 0 < tau.num) :
    0 < (inverse tau ht).num := tau.den_pos

theorem inverse_product (tau : Fraction) (ht : 0 < tau.num) :
    Fraction.equiv (Fraction.mul tau (inverse tau ht)) (Fraction.ofInt 1) := by
  simp only [inverse, Fraction.equiv, Fraction.mul, Fraction.ofInt]
  ac_nf

def norm (tau : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (pointNorm s.1) (Fraction.mul tau (pointNorm s.2))

def distance (tau : Fraction) (s t : Point × Point) : Fraction :=
  Fraction.add (pointDistance s.1 t.1) (Fraction.mul tau (pointDistance s.2 t.2))

/-- The actual drift and kick increments, in the chosen calibrated gauge. -/
theorem cell_increment (tau h : Fraction) (a : Point → Point) (s : Point × Point) :
    Fraction.equiv (distance tau (cell a h s) s)
      (Fraction.mul h.abs
        (Fraction.add (pointNorm s.2) (Fraction.mul tau (pointNorm (a (cell a h s).1))))) := by
  have hp := Fraction.equiv_trans
    (pointNorm_equiv (ConvexCover.drift_offset h s.1 s.2)) (pointNorm_scale h s.2)
  have hv := Fraction.equiv_trans
    (pointNorm_equiv (ConvexCover.drift_offset h s.2 (a (cell a h s).1)))
    (pointNorm_scale h (a (cell a h s).1))
  exact Fraction.equiv_trans
    (Fraction.add_equiv hp (Fraction.mul_equiv_left tau hv)) (by
      simp only [Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
      ac_nf)

theorem cell_increment_bound (tau h B V : Fraction) (a : Point → Point)
    (s : Point × Point) (ht : 0 ≤ tau.num)
    (hv : Fraction.le (pointNorm s.2) V)
    (ha : Fraction.le (pointNorm (a (cell a h s).1)) B) :
    Fraction.le (distance tau (cell a h s) s)
      (Fraction.mul h.abs (Fraction.add V (Fraction.mul tau B))) :=
  Fraction.le_equiv_left (cell_increment tau h a s)
    (Fraction.mul_le_mul_nonnegative_left
      (Fraction.add_le_add hv (Fraction.mul_le_mul_nonnegative_left ha tau ht))
      h.abs (Fraction.abs_num_nonnegative h))

theorem distance_self_zero (tau : Fraction) (s : Point × Point) :
    Fraction.equiv (distance tau s s) (Fraction.ofInt 0) :=
  Fraction.equiv_trans
    (Fraction.add_equiv (pointDistance_self_zero s.1)
      (Fraction.mul_equiv (Fraction.equiv_refl tau) (pointDistance_self_zero s.2)))
    (by simp [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt])

theorem distance_symm (tau : Fraction) (s t : Point × Point) :
    Fraction.equiv (distance tau s t) (distance tau t s) :=
  Fraction.add_equiv (pointDistance_symm s.1 t.1)
    (Fraction.mul_equiv_left tau (pointDistance_symm s.2 t.2))

theorem distance_triangle (tau : Fraction) (ht : 0 < tau.num)
    (s t u : Point × Point) :
    Fraction.le (distance tau s u)
      (Fraction.add (distance tau s t) (distance tau t u)) := by
  have hsum := Fraction.add_le_add (pointDistance_triangle s.1 t.1 u.1)
    (Fraction.mul_le_mul_nonnegative_left (pointDistance_triangle s.2 t.2 u.2)
      tau (Int.le_of_lt ht))
  apply Fraction.le_equiv_right hsum
  simp only [distance,Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
  ac_nf

def amplification (tau h L : Fraction) (ht : 0 < tau.num) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs (inverse tau ht)))
    (Fraction.add (Fraction.ofInt 1) (Fraction.mul (Fraction.mul h.abs tau) L))

def rate (tau L : Fraction) (ht : 0 < tau.num) : Fraction :=
  Fraction.add (inverse tau ht) (Fraction.mul tau L)

def rescaleState (c : Fraction) (hc : 0 < c.num) (s : Point × Point) : Point × Point :=
  (s.1,pointScale (inverse c hc) s.2)

def rescaleConstant (c L : Fraction) (hc : 0 < c.num) : Fraction :=
  Fraction.mul (Fraction.mul (inverse c hc) (inverse c hc)) L

theorem norm_rescale (c tau : Fraction) (s : Point × Point)
    (hc : 0 < c.num) :
    Fraction.equiv (norm (Fraction.mul c tau) (rescaleState c hc s)) (norm tau s) := by
  have hn := Fraction.equiv_trans (pointNorm_scale (inverse c hc) s.2)
    (Fraction.mul_equiv (Fraction.abs_of_nonnegative _ (Int.le_of_lt c.den_pos))
      (Fraction.equiv_refl _))
  apply Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _)
    (Fraction.mul_equiv (Fraction.equiv_refl _) hn))
  simp only [norm, rescaleState, inverse, Fraction.equiv, Fraction.add, Fraction.mul,
    Int.add_mul, Int.mul_add]
  ac_nf

theorem amplification_rescale (c tau h L : Fraction)
    (hc : 0 < c.num) (ht : 0 < tau.num) :
    Fraction.equiv
      (amplification (Fraction.mul c tau) (Fraction.mul c h)
        (rescaleConstant c L hc) (Int.mul_pos hc ht))
      (amplification tau h L ht) := by
  have hab := Fraction.equiv_trans (Fraction.abs_mul c h)
    (Fraction.mul_equiv (Fraction.abs_of_nonnegative c (Int.le_of_lt hc))
      (Fraction.equiv_refl _))
  unfold amplification
  apply Fraction.mul_equiv
  · apply Fraction.add_equiv (Fraction.equiv_refl _)
    apply Fraction.equiv_trans (Fraction.mul_equiv hab (Fraction.equiv_refl _))
    simp only [rescaleConstant, inverse, Fraction.equiv, Fraction.mul]
    ac_nf
  · apply Fraction.add_equiv (Fraction.equiv_refl _)
    apply Fraction.equiv_trans (Fraction.mul_equiv
      (Fraction.mul_equiv hab (Fraction.equiv_refl _)) (Fraction.equiv_refl _))
    simp only [rescaleConstant, inverse, Fraction.equiv, Fraction.mul]
    ac_nf

theorem window_rescale (c tau T L : Fraction)
    (hc : 0 < c.num) (ht : 0 < tau.num) :
    Fraction.equiv
      (Fraction.mul (Fraction.mul c T)
        (rate (Fraction.mul c tau) (rescaleConstant c L hc) (Int.mul_pos hc ht)))
      (Fraction.mul T (rate tau L ht)) := by
  simp only [rate, rescaleConstant, inverse, Fraction.equiv, Fraction.add,
    Fraction.mul, Int.add_mul, Int.mul_add]
  ac_nf

set_option maxHeartbeats 500000 in
theorem component_amplification (tau P V H L E : Fraction)
    (ht : 0 < tau.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num)
    (hH : 0 ≤ H.num) (hL : 0 ≤ L.num) :
    Fraction.le
      (Fraction.add (Fraction.add P (Fraction.mul H V))
        (Fraction.mul tau (Fraction.add V (Fraction.mul H
          (Fraction.add (Fraction.mul L (Fraction.add P (Fraction.mul H V))) E)))))
      (Fraction.add
        (Fraction.mul (amplification tau H L ht)
          (Fraction.add P (Fraction.mul tau V)))
        (Fraction.mul (Fraction.mul tau H) E)) := by
  let A := Fraction.add (Fraction.add P (Fraction.mul H V))
    (Fraction.mul tau (Fraction.add V (Fraction.mul H
      (Fraction.add (Fraction.mul L (Fraction.add P (Fraction.mul H V))) E))))
  let S := Fraction.add (Fraction.mul (Fraction.mul H (inverse tau ht)) P)
    (Fraction.add
      (Fraction.mul (Fraction.mul (Fraction.mul (Fraction.mul tau tau) H) L) V)
      (Fraction.mul (Fraction.mul (Fraction.mul H H) L) P))
  have hS : 0 ≤ S.num := Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_mul _ _ hH (Int.le_of_lt tau.den_pos)) hP)
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _
        (Fraction.nonnegative_mul _ _
          (Fraction.nonnegative_mul _ _
            (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) (Int.le_of_lt ht)) hH) hL) hV)
      (Fraction.nonnegative_mul _ _
        (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hH hH) hL) hP))
  have hbase := Fraction.le_add_nonnegative A S hS
  let K := Fraction.mul (Fraction.add (Fraction.ofInt 1) (Fraction.mul H (inverse tau ht)))
    (Fraction.add (Fraction.ofInt 1) (Fraction.mul (Fraction.mul H tau) L))
  have he : Fraction.equiv (Fraction.add A S)
      (Fraction.add (Fraction.mul K (Fraction.add P (Fraction.mul tau V)))
        (Fraction.mul (Fraction.mul tau H) E)) := by
    simp only [A,S,K,inverse,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.add_mul,Int.mul_add,Int.mul_one,Int.one_mul]
    ac_nf
  have hk : Fraction.equiv K (amplification tau H L ht) :=
    Fraction.mul_equiv
      (Fraction.add_equiv (Fraction.equiv_refl _)
        (Fraction.mul_equiv (Fraction.equiv_symm (Fraction.abs_of_nonnegative H hH))
          (Fraction.equiv_refl _)))
      (Fraction.add_equiv (Fraction.equiv_refl _)
        (Fraction.mul_equiv
          (Fraction.mul_equiv (Fraction.equiv_symm (Fraction.abs_of_nonnegative H hH))
            (Fraction.equiv_refl _)) (Fraction.equiv_refl _)))
  exact Fraction.le_equiv_right hbase
    (Fraction.equiv_trans he (Fraction.add_equiv
      (Fraction.mul_equiv hk (Fraction.equiv_refl _)) (Fraction.equiv_refl _)))

theorem cell_amplification (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E : Fraction) (s t : Point × Point)
    (hL : 0 ≤ L.num) (hc : comparisonContract a b L E) :
    Fraction.le (distance tau (cell a h s) (cell b h t))
      (Fraction.add (Fraction.mul (amplification tau h L ht) (distance tau s t))
        (Fraction.mul (Fraction.mul tau h.abs) E)) := by
  have hp := cell_position_perturbation a b h s t
  have hv := cell_velocity_perturbation a b h L E s t hc
  have ha := Fraction.add_le_add_left
    (Fraction.mul_le_mul_nonnegative_left
      (Fraction.add_le_add_right
        (Fraction.mul_le_mul_nonnegative_left hp L hL) E)
      h.abs (Fraction.abs_num_nonnegative h)) (pointDistance s.2 t.2)
  have hvc := Fraction.magnitudes.le_trans hv ha
  have hsum := Fraction.add_le_add hp
    (Fraction.mul_le_mul_nonnegative_left hvc tau (Int.le_of_lt ht))
  have hcomp := component_amplification tau (pointDistance s.1 t.1)
    (pointDistance s.2 t.2) h.abs L E ht
    (pointNorm_nonnegative _) (pointNorm_nonnegative _)
    (Fraction.abs_num_nonnegative h) hL
  have hh : h.abs.abs = h.abs := by simp only [Fraction.abs, Int.natAbs_ofNat]
  have hbound := Fraction.magnitudes.le_trans hsum hcomp
  simpa only [distance, amplification, hh] using hbound

theorem sampling_term_rescale (c tau h E : Fraction) (hc : 0 < c.num) :
    Fraction.equiv
      (Fraction.mul (Fraction.mul (Fraction.mul c tau) (Fraction.mul c h).abs)
        (rescaleConstant c E hc))
      (Fraction.mul (Fraction.mul tau h.abs) E) := by
  have ha := Fraction.equiv_trans (Fraction.abs_mul c h)
    (Fraction.mul_equiv (Fraction.abs_of_nonnegative c (Int.le_of_lt hc))
      (Fraction.equiv_refl _))
  apply Fraction.equiv_trans (Fraction.mul_equiv
    (Fraction.mul_equiv (Fraction.equiv_refl _) ha) (Fraction.equiv_refl _))
  simp only [rescaleConstant,inverse,Fraction.equiv,Fraction.mul]
  ac_nf

theorem distance_rescale (c tau : Fraction) (s t : Point × Point) (hc : 0 < c.num) :
    Fraction.equiv
      (distance (Fraction.mul c tau) (rescaleState c hc s) (rescaleState c hc t))
      (distance tau s t) := by
  have hv := Fraction.equiv_trans (difference_scale (inverse c hc) s.2 t.2)
    (Fraction.mul_equiv (Fraction.abs_of_nonnegative _ (Int.le_of_lt c.den_pos))
      (Fraction.equiv_refl _))
  apply Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _)
    (Fraction.mul_equiv (Fraction.equiv_refl _) hv))
  simp only [distance,rescaleState,inverse,Fraction.equiv,Fraction.add,Fraction.mul,
    Int.add_mul,Int.mul_add]
  ac_nf

theorem norm_unit_calibration (s : Point × Point) :
    Fraction.equiv (norm (Fraction.ofInt 1) s) (stateNorm s) := by
  simp only [norm,stateNorm,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.mul_one,Int.one_mul]

/-- The calibrated distance is a finite rescaling of the ordinary coordinate gauge. -/
theorem distance_le_uncalibrated (tau : Fraction) (ht : 0 < tau.num)
    (s t : Point × Point) :
    Fraction.le (distance tau s t)
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) tau) (stateDistance s t)) := by
  let C := Fraction.add (Fraction.ofInt 1) tau
  have hone : Fraction.le (Fraction.ofInt 1) C :=
    Fraction.le_add_nonnegative _ _ (Int.le_of_lt ht)
  have htau : Fraction.le tau C := Fraction.le_equiv_right
    (Fraction.le_add_nonnegative tau (Fraction.ofInt 1) (by decide))
    (Fraction.add_comm tau (Fraction.ofInt 1))
  have hp := Fraction.mul_le_mul_nonnegative hone (pointDistance s.1 t.1)
    (pointNorm_nonnegative _)
  have hv := Fraction.mul_le_mul_nonnegative htau (pointDistance s.2 t.2)
    (pointNorm_nonnegative _)
  have hsum := Fraction.add_le_add hp hv
  have hl : Fraction.equiv
      (Fraction.add (Fraction.mul (Fraction.ofInt 1) (pointDistance s.1 t.1))
        (Fraction.mul tau (pointDistance s.2 t.2))) (distance tau s t) := by
    simp only [distance,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one]
  have hr : Fraction.equiv
      (Fraction.add (Fraction.mul C (pointDistance s.1 t.1))
        (Fraction.mul C (pointDistance s.2 t.2)))
      (Fraction.mul C (stateDistance s t)) :=
    Fraction.equiv_symm (Fraction.mul_add C _ _)
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.equiv_symm hl) hsum) hr

theorem uncalibrated_le_distance (tau : Fraction) (ht : 0 < tau.num)
    (s t : Point × Point) :
    Fraction.le (stateDistance s t)
      (Fraction.mul (Fraction.add (Fraction.ofInt 1) (inverse tau ht))
        (distance tau s t)) := by
  let C := Fraction.add (Fraction.ofInt 1) (inverse tau ht)
  have hone : Fraction.le (Fraction.ofInt 1) C :=
    Fraction.le_add_nonnegative _ _ (Int.le_of_lt tau.den_pos)
  have hct : Fraction.equiv (Fraction.mul C tau)
      (Fraction.add tau (Fraction.ofInt 1)) := by
    simp only [C,inverse,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  have hvt : Fraction.le (Fraction.ofInt 1) (Fraction.mul C tau) :=
    Fraction.le_equiv_right (Fraction.le_add_nonnegative _ tau (Int.le_of_lt ht))
      (Fraction.equiv_symm (Fraction.equiv_trans hct (Fraction.add_comm _ _)))
  have hp := Fraction.mul_le_mul_nonnegative hone (pointDistance s.1 t.1)
    (pointNorm_nonnegative _)
  have hv := Fraction.mul_le_mul_nonnegative hvt (pointDistance s.2 t.2)
    (pointNorm_nonnegative _)
  have hsum := Fraction.add_le_add hp hv
  have hl : Fraction.equiv
      (Fraction.add (Fraction.mul (Fraction.ofInt 1) (pointDistance s.1 t.1))
        (Fraction.mul (Fraction.ofInt 1) (pointDistance s.2 t.2)))
      (stateDistance s t) := by
    simp only [stateDistance,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.one_mul,Int.mul_one]
  have hr : Fraction.equiv
      (Fraction.add (Fraction.mul C (pointDistance s.1 t.1))
        (Fraction.mul (Fraction.mul C tau) (pointDistance s.2 t.2)))
      (Fraction.mul C (distance tau s t)) := by
    simp only [distance,Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
    ac_nf
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.equiv_symm hl) hsum) hr

def CalibratedCauchy (tau : Fraction) (a : Nat → Point × Point) : Prop :=
  ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ m n : Nat,
    N ≤ m → N ≤ n → Fraction.lt (distance tau (a m) (a n)) eps

theorem calibrated_tolerance (tau eps : Fraction) (ht : 0 < tau.num)
    (s t : Point × Point)
    (hd : Fraction.lt (stateDistance s t)
      (HarmonicTimeRealization.factorDelta (Fraction.add (Fraction.ofInt 1) tau) eps
        (Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt ht)))) :
    Fraction.lt (distance tau s t) eps := by
  let C := Fraction.add (Fraction.ofInt 1) tau
  have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt ht)
  have hs := HarmonicTimeRealization.factor_control C eps (stateDistance s t) hC
    (Fraction.nonnegative_add _ _ (pointNorm_nonnegative _) (pointNorm_nonnegative _)) hd
  exact Fraction.magnitudes.lt_of_le_lt (distance_le_uncalibrated tau ht s t)
    (Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.equiv_symm (Fraction.mul_comm (stateDistance s t) C))) hs)

theorem unit_tolerance (tau eps : Fraction) (ht : 0 < tau.num)
    (s t : Point × Point)
    (hd : Fraction.lt (distance tau s t)
      (HarmonicTimeRealization.factorDelta
        (Fraction.add (Fraction.ofInt 1) (inverse tau ht)) eps
        (Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos)))) :
    Fraction.lt (stateDistance s t) eps := by
  let C := Fraction.add (Fraction.ofInt 1) (inverse tau ht)
  have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt tau.den_pos)
  have hs := HarmonicTimeRealization.factor_control C eps (distance tau s t) hC
    (Fraction.nonnegative_add _ _ (pointNorm_nonnegative _)
      (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) (pointNorm_nonnegative _))) hd
  exact Fraction.magnitudes.lt_of_le_lt (uncalibrated_le_distance tau ht s t)
    (Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.equiv_symm (Fraction.mul_comm (distance tau s t) C))) hs)

theorem distance_unit_calibration (s t : Point × Point) :
    Fraction.equiv (distance (Fraction.ofInt 1) s t) (stateDistance s t) := by
  simp only [distance,stateDistance,Fraction.equiv,Fraction.add,Fraction.mul,
    Fraction.ofInt,Int.one_mul,Int.mul_one]

theorem cauchy_calibration_iff (tau : Fraction) (ht : 0 < tau.num)
    (a : Nat → Point × Point) :
    CalibratedCauchy tau a ↔ CalibratedCauchy (Fraction.ofInt 1) a := by
  constructor
  · intro ha eps heps
    let C := Fraction.add (Fraction.ofInt 1) (inverse tau ht)
    have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide)
      (Int.le_of_lt tau.den_pos)
    obtain ⟨N,hN⟩ := ha (HarmonicTimeRealization.factorDelta C eps hC)
      (HarmonicTimeRealization.factorDelta_positive C eps hC heps)
    exact ⟨N,fun m n hm hn => Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (distance_unit_calibration (a m) (a n)))
      (unit_tolerance tau eps ht (a m) (a n) (hN m n hm hn))⟩
  · intro ha eps heps
    let C := Fraction.add (Fraction.ofInt 1) tau
    have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt ht)
    obtain ⟨N,hN⟩ := ha (HarmonicTimeRealization.factorDelta C eps hC)
      (HarmonicTimeRealization.factorDelta_positive C eps hC heps)
    exact ⟨N,fun m n hm hn => calibrated_tolerance tau eps ht (a m) (a n)
      (Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_of_equiv (Fraction.equiv_symm (distance_unit_calibration (a m) (a n))))
        (hN m n hm hn))⟩

def CalibratedEquivalent (tau : Fraction) (a b : Nat → Point × Point) : Prop :=
  ∀ eps : Fraction, 0 < eps.num → ∃ N : Nat, ∀ n : Nat,
    N ≤ n → Fraction.lt (distance tau (a n) (b n)) eps

/-- The actual completed value relation is unchanged by a fixed calibration. -/
theorem nameEquiv_calibration_iff (tau : Fraction) (ht : 0 < tau.num)
    (a b : HarmonicDyadic.EndpointCauchyName) :
    CalibratedEquivalent tau a.approx b.approx ↔ CauchyValues.NameEquiv a b := by
  constructor
  · intro ha eps heps
    let C := Fraction.add (Fraction.ofInt 1) (inverse tau ht)
    have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide)
      (Int.le_of_lt tau.den_pos)
    obtain ⟨N,hN⟩ := ha (HarmonicTimeRealization.factorDelta C eps hC)
      (HarmonicTimeRealization.factorDelta_positive C eps hC heps)
    exact ⟨N,fun n hn => unit_tolerance tau eps ht (a.approx n) (b.approx n) (hN n hn)⟩
  · intro ha eps heps
    let C := Fraction.add (Fraction.ofInt 1) tau
    have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide) (Int.le_of_lt ht)
    obtain ⟨N,hN⟩ := ha (HarmonicTimeRealization.factorDelta C eps hC)
      (HarmonicTimeRealization.factorDelta_positive C eps hC heps)
    exact ⟨N,fun n hn => calibrated_tolerance tau eps ht
      (a.approx n) (b.approx n) (hN n hn)⟩

theorem amplification_nonnegative (tau h L : Fraction)
    (ht : 0 < tau.num) (hL : 0 ≤ L.num) :
    0 ≤ (amplification tau h L ht).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_add _ _ (by decide)
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
        (Int.le_of_lt tau.den_pos)))
    (Fraction.nonnegative_add _ _ (by decide)
      (Fraction.nonnegative_mul _ _
        (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h) (Int.le_of_lt ht)) hL))

theorem one_le_amplification (tau h L : Fraction)
    (ht : 0 < tau.num) (hL : 0 ≤ L.num) :
    Fraction.le (Fraction.ofInt 1) (amplification tau h L ht) := by
  have hp := Fraction.le_add_nonnegative (Fraction.ofInt 1)
    (Fraction.mul h.abs (inverse tau ht))
    (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
      (Int.le_of_lt tau.den_pos))
  have hq := Fraction.le_add_nonnegative (Fraction.ofInt 1)
    (Fraction.mul (Fraction.mul h.abs tau) L)
    (Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h) (Int.le_of_lt ht)) hL)
  have hfirst := Fraction.mul_le_mul_nonnegative_left hq
    (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs (inverse tau ht)))
    (Fraction.nonnegative_add _ _ (by decide)
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
        (Int.le_of_lt tau.den_pos)))
  have hp' : Fraction.le (Fraction.ofInt 1)
      (Fraction.mul
        (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs (inverse tau ht)))
        (Fraction.ofInt 1)) := Fraction.le_equiv_right hp (by
    simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one])
  exact Fraction.magnitudes.le_trans hp' hfirst

def Window (tau h L : Fraction) (ht : 0 < tau.num) (n : Nat) : Prop :=
  Fraction.le (Fraction.mul (Fraction.ofInt (n : Int))
    (Fraction.mul h.abs (rate tau L ht))) ⟨1,2,by decide⟩

theorem rate_nonnegative (tau L : Fraction) (ht : 0 < tau.num)
    (hL : 0 ≤ L.num) : 0 ≤ (rate tau L ht).num :=
  Fraction.nonnegative_add _ _ (Int.le_of_lt tau.den_pos)
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) hL)

theorem window_mono (tau h L : Fraction) (ht : 0 < tau.num)
    (hL : 0 ≤ L.num) (n N : Nat) (hn : n ≤ N) (hs : Window tau h L ht N) :
    Window tau h L ht n := by
  have hc : Fraction.le (Fraction.ofInt (n : Int)) (Fraction.ofInt (N : Int)) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one] using
      (show (n : Int) ≤ (N : Int) by omega)
  exact Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative hc (Fraction.mul h.abs (rate tau L ht))
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
        (rate_nonnegative tau L ht hL))) hs

theorem window_of_elapsed (tau h T L : Fraction) (ht : 0 < tau.num)
    (hL : 0 ≤ L.num) (n : Nat)
    (he : Fraction.le (Fraction.mul (Fraction.ofInt (n : Int)) h.abs) T)
    (hs : Fraction.le (Fraction.mul T (rate tau L ht)) ⟨1,2,by decide⟩) :
    Window tau h L ht n := by
  have hm := Fraction.mul_le_mul_nonnegative he (rate tau L ht)
    (rate_nonnegative tau L ht hL)
  exact Fraction.le_equiv_left
    (Fraction.equiv_symm (Fraction.mul_assoc (Fraction.ofInt (n : Int)) h.abs (rate tau L ht)))
    (Fraction.magnitudes.le_trans hm hs)

/-- The factors are h/tau and tau*h*L; their product is h²*L. -/
theorem amplification_expansion (tau h L : Fraction) (ht : 0 < tau.num) :
    Fraction.equiv (amplification tau h L ht)
      (Fraction.add (Fraction.ofInt 1)
        (Fraction.add (Fraction.mul h.abs (rate tau L ht))
          (Fraction.mul (Fraction.mul h.abs h.abs) L))) := by
  simp only [amplification,rate,inverse,Fraction.equiv,Fraction.add,Fraction.mul,
    Fraction.ofInt,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

theorem amplification_power_le_two (tau h L : Fraction)
    (ht : 0 < tau.num) (hL : 0 ≤ L.num) (n : Nat)
    (hs : Window tau h L ht n) :
    Fraction.le (HarmonicAccumulation.fpower (amplification tau h L ht) n)
      (Fraction.ofInt 2) := by
  apply FiniteFactorProducts.repeated_pair_le_two
    (Fraction.mul h.abs (inverse tau ht))
    (Fraction.mul (Fraction.mul h.abs tau) L) n
    (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h)
      (Int.le_of_lt tau.den_pos))
    (Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative h) (Int.le_of_lt ht)) hL)
  apply Fraction.le_equiv_left (b := Fraction.mul (Fraction.ofInt (n : Int))
    (Fraction.mul h.abs (rate tau L ht))) _ hs
  simp only [rate,Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
  ac_nf

/-- Actual sampled schedules, starting at the same state, accumulate the
calibrated sample discrepancy without assuming a motion error estimate. -/
theorem run_distance_le_source (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hc : comparisonContract a b L E) :
    (n : Nat) → Fraction.le
      (distance tau (BoundedIteration.run a h s n) (BoundedIteration.run b h s n))
      (FiniteRecurrence.sourceBudget (amplification tau h L ht)
        (Fraction.mul (Fraction.mul tau h.abs) E) n)
  | 0 => by
      apply Fraction.le_of_equiv
      simp only [distance,BoundedIteration.run,FiniteRecurrence.sourceBudget]
      exact Fraction.equiv_trans
        (Fraction.add_equiv (pointDistance_self_zero s.1)
          (Fraction.mul_equiv (Fraction.equiv_refl tau) (pointDistance_self_zero s.2)))
        (by simp [FiniteRecurrence.sourceBudget,Fraction.equiv,Fraction.add,
          Fraction.mul,Fraction.ofInt])
  | n+1 => by
      have hstep := cell_amplification tau ht a b h L E
        (BoundedIteration.run a h s n) (BoundedIteration.run b h s n) hL hc
      have hnext := Fraction.add_le_add_right
        (Fraction.mul_le_mul_nonnegative_left
          (run_distance_le_source tau ht a b h L E s hL hc n)
          (amplification tau h L ht) (amplification_nonnegative tau h L ht hL))
        (Fraction.mul (Fraction.mul tau h.abs) E)
      exact Fraction.magnitudes.le_trans hstep hnext

theorem run_uniform_discrepancy (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (h L E : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hc : comparisonContract a b L E)
    (n : Nat) (hs : Window tau h L ht n) :
    Fraction.le
      (distance tau (BoundedIteration.run a h s n) (BoundedIteration.run b h s n))
      (Fraction.mul (Fraction.ofInt (2 * (n : Int)))
        (Fraction.mul (Fraction.mul tau h.abs) E)) := by
  let K := amplification tau h L ht
  let S := Fraction.mul (Fraction.mul tau h.abs) E
  have hK := amplification_nonnegative tau h L ht hL
  have hS : 0 ≤ S.num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) (Fraction.abs_num_nonnegative h)) hE
  have hp := amplification_power_le_two tau h L ht hL n hs
  exact Fraction.magnitudes.le_trans
    (run_distance_le_source tau ht a b h L E s hL hc n)
    (FiniteRecurrence.sourceBudget_two_count K S n hK hS
      (one_le_amplification tau h L ht hL) hp)

/-- Time-unit rescaling preserves the actual-family Cauchy condition. -/
theorem cauchy_rescale (c tau : Fraction) (hc : 0 < c.num)
    (a : Nat → Point × Point) :
    CalibratedCauchy (Fraction.mul c tau) (fun n => rescaleState c hc (a n)) ↔
      CalibratedCauchy tau a := by
  constructor
  · intro ha eps heps
    obtain ⟨N,hN⟩ := ha eps heps
    refine ⟨N,fun m n hm hn => ?_⟩
    exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.equiv_symm (distance_rescale c tau (a m) (a n) hc)))
      (hN m n hm hn)
  · intro ha eps heps
    obtain ⟨N,hN⟩ := ha eps heps
    refine ⟨N,fun m n hm hn => ?_⟩
    exact Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (distance_rescale c tau (a m) (a n) hc))
      (hN m n hm hn)

theorem window_rescale_iff (c tau h L : Fraction)
    (hc : 0 < c.num) (ht : 0 < tau.num) (n : Nat) :
    Window (Fraction.mul c tau) (Fraction.mul c h) (rescaleConstant c L hc)
      (Int.mul_pos hc ht) n ↔ Window tau h L ht n := by
  have ha := Fraction.equiv_trans (Fraction.abs_mul c h)
    (Fraction.mul_equiv (Fraction.abs_of_nonnegative c (Int.le_of_lt hc))
      (Fraction.equiv_refl h.abs))
  have hw := Fraction.equiv_trans
    (Fraction.mul_equiv ha (Fraction.equiv_refl _))
    (window_rescale c tau h.abs L hc ht)
  have he := Fraction.mul_equiv (Fraction.equiv_refl (Fraction.ofInt (n : Int))) hw
  constructor
  · intro hs
    exact Fraction.le_equiv_left (Fraction.equiv_symm he) hs
  · intro hs
    exact Fraction.le_equiv_left he hs

private def two : Fraction := Fraction.ofInt 2
private def three : Fraction := Fraction.ofInt 3
private def half : Fraction := ⟨1,2,by decide⟩
private def quarter : Fraction := ⟨1,4,by decide⟩
private def sampleState : Point × Point :=
  ((Fraction.ofInt 1,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 1))

theorem rescaling_control :
    Fraction.equiv (norm two sampleState)
      (norm (Fraction.mul three two) (rescaleState three (by decide) sampleState)) ∧
    Fraction.equiv (amplification two quarter (Fraction.ofInt 1) (by decide))
      (amplification (Fraction.mul three two) (Fraction.mul three quarter)
        (rescaleConstant three (Fraction.ofInt 1) (by decide)) (by decide)) := by decide

theorem uncalibrated_norm_changes_control :
    ¬ Fraction.equiv (stateNorm sampleState)
      (stateNorm (rescaleState two (by decide) sampleState)) := by decide

theorem zero_lipschitz_control :
    Fraction.equiv (amplification two half (Fraction.ofInt 0) (by decide))
      ⟨5,4,by decide⟩ := by decide

end NewtonLimitDynamics.Polygon.TimeCalibration
