import BarrowLib.Polygon.KinematicEstimates

/-! Actual finite velocity remainders relative to the force at a cell's
starting point. Position displacement and force comparison derive the error;
no derivative, completed motion or force equation is supplied. -/

namespace NewtonLimitDynamics.Polygon.AccelerationEstimates
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates BoundedIteration KinematicEstimates

theorem position_increment (a : Point → Point) (h : Fraction) (s : Point × Point) :
    Fraction.equiv (pointDistance (cell a h s).1 s.1)
      (Fraction.mul h.abs (pointNorm s.2)) :=
  Fraction.equiv_trans (pointNorm_equiv (ConvexCover.drift_offset h s.1 s.2))
    (pointNorm_scale h s.2)

theorem position_displacement (a : Point → Point) (h : Fraction) (s : Point × Point)
    (V : Fraction) (hh : 0 ≤ h.num) (N n : Nat) (hn : n ≤ N)
    (hv : ∀ i, i < N → Fraction.le (pointNorm (run a h s i).2) V) :
    Fraction.le (pointDistance (run a h s n).1 s.1) (Fraction.mul (time h n) V) := by
  have hs : ∀ i, i<N → Fraction.le
      (pointDistance (run a h s (i+1)).1 (run a h s i).1) (Fraction.mul h V) := by
    intro i hi
    exact Fraction.le_equiv_left (position_increment a h (run a h s i))
      (Fraction.le_equiv_right
        (Fraction.mul_le_mul_nonnegative_left (hv i hi) h.abs (Fraction.abs_num_nonnegative h))
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl V)))
  have hg := FiniteSequenceGap.finite_gap
    (fun (x y : Point × Point) => (pointDistance x.1 y.1).toRat)
    (fun x => by
      have hx := (Fraction.equiv_iff_toRat _ _).mp (pointDistance_self_zero x.1)
      simpa only [Fraction.toRat_ofInt, Rat.intCast_zero] using hx)
    (fun x y z => by
      have ht := (Fraction.le_iff_toRat _ _).mp (pointDistance_triangle x.1 y.1 z.1)
      simpa only [Fraction.toRat_add] using ht)
    (run a h s) N (Fraction.mul h V).toRat
    (fun i hi => (Fraction.le_iff_toRat _ _).mp (hs i hi)) 0 n (by omega)
  apply (Fraction.le_iff_toRat _ _).mpr
  simpa only [Nat.zero_add, run, time, Fraction.toRat_mul, Fraction.toRat_ofInt,
    Rat.intCast_ofNat, Rat.mul_assoc] using! hg

def predictedVelocity (a : Point → Point) (h : Fraction) (s : Point × Point) (n : Nat) : Point :=
  inertialPosition h (s.2,a s.1) n

theorem velocity_remainder_from_samples (a : Point → Point) (h : Fraction)
    (s : Point × Point) (C : Fraction) (hh : 0 ≤ h.num) (N : Nat)
    (hs : ∀ i, i<N → Fraction.le (pointDistance (a (run a h s (i+1)).1) (a s.1)) C) :
    ∀ n, n ≤ N → Fraction.le (pointDistance (run a h s n).2 (predictedVelocity a h s n))
      (Fraction.mul (time h n) C) := by
  intro n hn
  induction n with
  | zero =>
    have he := inertial_zero h (s.2,a s.1)
    apply Fraction.le_of_equiv
    apply Fraction.equiv_trans (pointDistance_equiv
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ he)
    apply Fraction.equiv_trans (pointDistance_self_zero s.2)
    simp [time,Fraction.equiv,Fraction.mul,Fraction.ofInt]
  | succ n ih =>
    have hf := Fraction.le_equiv_left (difference_scale h _ _)
      (Fraction.le_equiv_right
        (Fraction.mul_le_mul_nonnegative_left (hs n (by omega)) h.abs (Fraction.abs_num_nonnegative h))
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl C)))
    have ha := difference_add_bound (run a h s n).2 (predictedVelocity a h s n)
      (pointScale h (a (run a h s (n+1)).1)) (pointScale h (a s.1))
    have hc := Fraction.magnitudes.le_trans ha (Fraction.add_le_add (ih (by omega)) hf)
    have hd := Fraction.le_equiv_left
      (pointDistance_equiv (p := (run a h s (n+1)).2)
        ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (inertial_step h (s.2,a s.1) n)) hc
    apply Fraction.le_equiv_right hd
    simp only [time,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf

def source (L E t V : Fraction) : Fraction :=
  Fraction.add (Fraction.mul L (Fraction.mul t V)) E

theorem force_variation_at (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hV : 0 ≤ V.num)
    (N i : Nat) (hi : i<N)
    (hc : Fraction.le (pointDistance (a (run a h s (i+1)).1) (a s.1))
      (Fraction.add (Fraction.mul L (pointDistance (run a h s (i+1)).1 s.1)) E))
    (hv : ∀ k, k<N → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (a (run a h s (i+1)).1) (a s.1))
      (source L E (time h N) V) := by
  have hp := Fraction.magnitudes.le_trans
    (position_displacement a h s V hh N (i+1) (by omega) hv)
    (Fraction.mul_le_mul_nonnegative (time_monotone h hh (i+1) N (by omega)) V hV)
  exact Fraction.magnitudes.le_trans hc
    (Fraction.add_le_add_right (Fraction.mul_le_mul_nonnegative_left hp L hL) E)


theorem force_variation (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hV : 0 ≤ V.num)
    (hc : comparisonContract a a L E) (N i : Nat) (hi : i<N)
    (hv : ∀ k, k<N → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (a (run a h s (i+1)).1) (a s.1))
      (source L E (time h N) V) :=
  force_variation_at a h s L E V hh hL hV N i hi (hc _ _) hv

theorem velocity_remainder_at (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hV : 0 ≤ V.num)
    (n : Nat)
    (hc : ∀ k, k<n → Fraction.le
      (pointDistance (a (run a h s (k+1)).1) (a s.1))
      (Fraction.add (Fraction.mul L (pointDistance (run a h s (k+1)).1 s.1)) E))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (run a h s n).2 (predictedVelocity a h s n))
      (Fraction.mul (time h n) (source L E (time h n) V)) :=
  velocity_remainder_from_samples a h s _ hh n
    (fun i hi => force_variation_at a h s L E V hh hL hV n i hi (hc i hi) hv) n (Nat.le_refl _)


theorem velocity_remainder (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hV : 0 ≤ V.num)
    (hc : comparisonContract a a L E) (n : Nat)
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (run a h s n).2 (predictedVelocity a h s n))
      (Fraction.mul (time h n) (source L E (time h n) V)) :=
  velocity_remainder_at a h s L E V hh hL hV n (fun _ _ => hc _ _) hv

theorem acceleration_secant_bound_at (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hV : 0 ≤ V.num)
    (n : Nat) (ht : 0 < (time h n).num)
    (hc : ∀ k, k<n → Fraction.le
      (pointDistance (a (run a h s (k+1)).1) (a s.1))
      (Fraction.add (Fraction.mul L (pointDistance (run a h s (k+1)).1 s.1)) E))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance
      (pointScale (TimeCalibration.inverse (time h n) ht) (pointSub (run a h s n).2 s.2))
      (a s.1)) (source L E (time h n) V) := by
  have he := Fraction.equiv_trans (pointNorm_equiv (secant_identity (time h n) ht
    (run a h s n).2 s.2 (a s.1)))
    (pointNorm_scale (TimeCalibration.inverse (time h n) ht)
      (pointSub (run a h s n).2 (predictedVelocity a h s n)))
  have hm := Fraction.mul_le_mul_nonnegative_left
    (velocity_remainder_at a h s L E V hh hL hV n hc hv)
    (TimeCalibration.inverse (time h n) ht).abs (Fraction.abs_num_nonnegative _)
  apply Fraction.le_equiv_right (Fraction.le_equiv_left he hm)
  rw [Fraction.abs_eq_of_nonnegative (TimeCalibration.inverse (time h n) ht)
    (Int.le_of_lt (time h n).den_pos)]
  simp only [TimeCalibration.inverse,Fraction.equiv,Fraction.mul]
  ac_nf


theorem acceleration_secant_bound (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hV : 0 ≤ V.num)
    (hc : comparisonContract a a L E) (n : Nat) (ht : 0 < (time h n).num)
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance
      (pointScale (TimeCalibration.inverse (time h n) ht) (pointSub (run a h s n).2 s.2))
      (a s.1)) (source L E (time h n) V) :=
  acceleration_secant_bound_at a h s L E V hh hL hV n ht (fun _ _ => hc _ _) hv

theorem acceleration_secant_equivalent_time_at (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V u : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hV : 0 ≤ V.num)
    (n : Nat) (ht : 0 < (time h n).num)
    (hc : ∀ k, k<n → Fraction.le
      (pointDistance (a (run a h s (k+1)).1) (a s.1))
      (Fraction.add (Fraction.mul L (pointDistance (run a h s (k+1)).1 s.1)) E))
    (hu : 0 < u.num) (he : Fraction.equiv u (time h n))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance
      (pointScale (TimeCalibration.inverse u hu) (pointSub (run a h s n).2 s.2))
      (a s.1)) (source L E u V) :=
  Fraction.le_equiv_right
    (Fraction.le_equiv_left (pointDistance_equiv
      (pointScale_ratio_congr (TimeCalibration.inverse_congr hu ht he)
        ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (acceleration_secant_bound_at a h s L E V hh hL hV n ht hc hv))
    (Fraction.add_equiv (Fraction.mul_equiv (Fraction.equiv_refl L)
      (Fraction.mul_equiv (Fraction.equiv_symm he) (Fraction.equiv_refl V))) (Fraction.equiv_refl E))


theorem acceleration_secant_equivalent_time (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V u : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hV : 0 ≤ V.num)
    (hc : comparisonContract a a L E) (n : Nat) (ht : 0 < (time h n).num)
    (hu : 0 < u.num) (he : Fraction.equiv u (time h n))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance
      (pointScale (TimeCalibration.inverse u hu) (pointSub (run a h s n).2 s.2))
      (a s.1)) (source L E u V) :=
  acceleration_secant_equivalent_time_at a h s L E V u hh hL hV n ht (fun _ _ => hc _ _) hu he hv

private def controlHalf : Fraction := ⟨1,2,by decide⟩
private def controlState : Point × Point :=
  ((Fraction.ofInt 1,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0))

theorem two_cell_acceleration_control :
    Fraction.equiv
      (pointDistance (pointScale (TimeCalibration.inverse (time controlHalf 2) (by decide))
        (pointSub (run pointNeg controlHalf controlState 2).2 controlState.2))
        (pointNeg controlState.1)) ⟨1,8,by decide⟩ := by decide

theorem zero_bound_rejects_acceleration_control :
    ¬ Fraction.le
      (pointDistance (pointScale (TimeCalibration.inverse (time controlHalf 2) (by decide))
        (pointSub (run pointNeg controlHalf controlState 2).2 controlState.2))
        (pointNeg controlState.1)) (Fraction.ofInt 0) := by unfold Fraction.le; decide

end NewtonLimitDynamics.Polygon.AccelerationEstimates
