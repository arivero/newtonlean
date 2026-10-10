import BarrowLib.Polygon.TimeCalibration
import BarrowLib.Polygon.FiniteSequenceGap

/-! Finite drift/kick remainders at actual sampled arrivals. The O(t²)
position remainder and O(t) velocity change are derived from the recurrence;
no derivative, curve, integral or ODE theorem is a premise. -/

namespace NewtonLimitDynamics.Polygon.KinematicEstimates
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates BoundedIteration

def inertialPosition (h : Fraction) (s : Point × Point) (n : Nat) : Point :=
  pointAdd s.1 (pointScale (time h n) s.2)

theorem inertial_zero (h : Fraction) (s : Point × Point) :
    pointEquiv (inertialPosition h s 0) s.1 := by
  constructor <;>
    simp only [inertialPosition,time,pointEquiv,pointAdd,pointScale,Fraction.equiv,
      Fraction.add,Fraction.mul,Fraction.ofInt,Int.natCast_zero,Int.zero_mul,
      Int.mul_zero,Int.add_zero,Int.one_mul,Int.mul_one] <;> ac_nf

theorem inertial_step (h : Fraction) (s : Point × Point) (n : Nat) :
    pointEquiv (inertialPosition h s (n+1))
      (pointAdd (inertialPosition h s n) (pointScale h s.2)) := by
  constructor <;>
    simp only [inertialPosition,time,pointEquiv,pointAdd,pointScale,Fraction.equiv,
      Fraction.add,Fraction.mul,Fraction.ofInt,Int.natCast_add,Int.natCast_one,
      Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one] <;> ac_nf

theorem velocity_increment (a : Point → Point) (h : Fraction) (s : Point × Point) :
    Fraction.equiv (pointDistance (cell a h s).2 s.2)
      (Fraction.mul h.abs (pointNorm (a (cell a h s).1))) :=
  Fraction.equiv_trans (pointNorm_equiv (ConvexCover.drift_offset h s.2 (a (cell a h s).1)))
    (pointNorm_scale h (a (cell a h s).1))

theorem velocity_displacement (a : Point → Point) (h : Fraction) (s : Point × Point)
    (B : Fraction) (hh : 0 ≤ h.num) (n : Nat) (hb : BoundedSamples a h s B n) :
    Fraction.le (pointDistance (run a h s n).2 s.2) (Fraction.mul (time h n) B) := by
  have hs : ∀ i, i<n → Fraction.le (pointDistance (run a h s (i+1)).2 (run a h s i).2)
      (Fraction.mul h B) := by
    intro i hi
    exact Fraction.le_equiv_left (velocity_increment a h (run a h s i))
      (Fraction.le_equiv_right
        (Fraction.mul_le_mul_nonnegative_left (hb i hi) h.abs (Fraction.abs_num_nonnegative h))
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl B)))
  have hg := FiniteSequenceGap.finite_gap
    (fun (x y : Point × Point) => (pointDistance x.2 y.2).toRat)
    (fun x => by
      have hx := (Fraction.equiv_iff_toRat _ _).mp (pointDistance_self_zero x.2)
      simpa only [Fraction.toRat_ofInt, Rat.intCast_zero] using hx)
    (fun x y z => by
      have ht := (Fraction.le_iff_toRat _ _).mp (pointDistance_triangle x.2 y.2 z.2)
      simpa only [Fraction.toRat_add] using ht)
    (run a h s) n (Fraction.mul h B).toRat
    (fun i hi => (Fraction.le_iff_toRat _ _).mp (hs i hi)) 0 n (by omega)
  apply (Fraction.le_iff_toRat _ _).mpr
  simpa only [Nat.zero_add, run, time, Fraction.toRat_mul, Fraction.toRat_ofInt,
    Rat.intCast_ofNat, Rat.mul_assoc] using! hg

theorem quadratic_step (h B : Fraction) (hh : 0 ≤ h.num) (hB : 0 ≤ B.num) (n : Nat) :
    Fraction.le
      (Fraction.add (Fraction.mul (Fraction.mul (time h n) (time h n)) B)
        (Fraction.mul h (Fraction.mul (time h n) B)))
      (Fraction.mul (Fraction.mul (time h (n+1)) (time h (n+1))) B) := by
  let A := Fraction.add (Fraction.mul (Fraction.mul (time h n) (time h n)) B)
    (Fraction.mul h (Fraction.mul (time h n) B))
  let E := Fraction.mul (Fraction.mul (time h (n+1)) h) B
  have hE : 0 ≤ E.num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ (time_nonnegative h hh _) hh) hB
  apply Fraction.le_equiv_right (Fraction.le_add_nonnegative A E hE)
  simp only [A,E,time,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf

/-- Position's actual finite remainder from its inertial continuation. -/
theorem position_remainder (a : Point → Point) (h : Fraction) (s : Point × Point)
    (B : Fraction) (hh : 0 ≤ h.num) (hB : 0 ≤ B.num) (n : Nat)
    (hb : BoundedSamples a h s B n) :
    Fraction.le (pointDistance (run a h s n).1 (inertialPosition h s n))
      (Fraction.mul (Fraction.mul (time h n) (time h n)) B) := by
  induction n with
  | zero =>
    have he := inertial_zero h s
    apply Fraction.le_of_equiv
    apply Fraction.equiv_trans (pointDistance_equiv
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ he)
    apply Fraction.equiv_trans (pointDistance_self_zero s.1)
    simp [time,Fraction.equiv,Fraction.mul,Fraction.ofInt]
  | succ n ih =>
    have hb0 : BoundedSamples a h s B n := fun i hi => hb i (by omega)
    have hv := velocity_displacement a h s B hh n hb0
    have hs := Fraction.le_equiv_left (difference_scale h (run a h s n).2 s.2)
      (Fraction.le_equiv_right
        (Fraction.mul_le_mul_nonnegative_left hv h.abs (Fraction.abs_num_nonnegative h))
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh)
          (Fraction.equiv_refl (Fraction.mul (time h n) B))))
    have ha := difference_add_bound (run a h s n).1 (inertialPosition h s n)
      (pointScale h (run a h s n).2) (pointScale h s.2)
    have hc := Fraction.magnitudes.le_trans ha (Fraction.add_le_add (ih hb0) hs)
    have hd := Fraction.le_equiv_left
      (pointDistance_equiv (p := (run a h s (n+1)).1) ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
        (inertial_step h s n)) hc
    exact Fraction.magnitudes.le_trans hd (quadratic_step h B hh hB n)

/-- The finite quotient remainder is obtained by dividing the derived remainder. -/
theorem secant_identity (t : Fraction) (ht : 0 < t.num) (p x v : Point) :
    pointEquiv
      (pointSub (pointScale (TimeCalibration.inverse t ht) (pointSub p x)) v)
      (pointScale (TimeCalibration.inverse t ht)
        (pointSub p (pointAdd x (pointScale t v)))) := by
  constructor <;>
    simp only [TimeCalibration.inverse,pointEquiv,pointSub,pointAdd,pointNeg,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;>
    ac_nf <;> omega

theorem position_secant_bound (a : Point → Point) (h : Fraction) (s : Point × Point)
    (B : Fraction) (hh : 0 ≤ h.num) (hB : 0 ≤ B.num) (n : Nat)
    (ht : 0 < (time h n).num) (hb : BoundedSamples a h s B n) :
    Fraction.le
      (pointDistance (pointScale (TimeCalibration.inverse (time h n) ht)
        (pointSub (run a h s n).1 s.1)) s.2)
      (Fraction.mul (time h n) B) := by
  have he := Fraction.equiv_trans (pointNorm_equiv (secant_identity (time h n) ht
    (run a h s n).1 s.1 s.2))
    (pointNorm_scale (TimeCalibration.inverse (time h n) ht)
      (pointSub (run a h s n).1 (inertialPosition h s n)))
  have hm := Fraction.mul_le_mul_nonnegative_left (position_remainder a h s B hh hB n hb)
    (TimeCalibration.inverse (time h n) ht).abs (Fraction.abs_num_nonnegative _)
  apply Fraction.le_equiv_right (Fraction.le_equiv_left he hm)
  rw [Fraction.abs_eq_of_nonnegative (TimeCalibration.inverse (time h n) ht)
    (Int.le_of_lt (time h n).den_pos)]
  simp only [TimeCalibration.inverse,Fraction.equiv,Fraction.mul]
  ac_nf

theorem position_secant_equivalent_time (a : Point → Point) (h : Fraction) (s : Point × Point)
    (B u : Fraction) (hh : 0 ≤ h.num) (hB : 0 ≤ B.num) (n : Nat)
    (ht : 0 < (time h n).num) (hu : 0 < u.num) (he : Fraction.equiv u (time h n))
    (hb : BoundedSamples a h s B n) :
    Fraction.le
      (pointDistance (pointScale (TimeCalibration.inverse u hu)
        (pointSub (run a h s n).1 s.1)) s.2) (Fraction.mul u B) :=
  Fraction.le_equiv_right
    (Fraction.le_equiv_left (pointDistance_equiv
      (pointScale_ratio_congr (TimeCalibration.inverse_congr hu ht he)
        ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (position_secant_bound a h s B hh hB n ht hb))
    (Fraction.mul_equiv (Fraction.equiv_symm he) (Fraction.equiv_refl B))

private def controlHalf : Fraction := ⟨1,2,by decide⟩
private def controlState : Point × Point :=
  ((Fraction.ofInt 0,Fraction.ofInt 0),(Fraction.ofInt 1,Fraction.ofInt 0))
private def controlForce (_ : Point) : Point := (Fraction.ofInt 0,Fraction.ofInt (-1))

theorem two_cell_secant_control :
    Fraction.equiv
      (pointDistance (pointScale (TimeCalibration.inverse (time controlHalf 2) (by decide))
        (pointSub (run controlForce controlHalf controlState 2).1 controlState.1)) controlState.2)
      ⟨1,4,by decide⟩ := by decide

theorem zero_bound_rejects_secant_control :
    ¬ Fraction.le
      (pointDistance (pointScale (TimeCalibration.inverse (time controlHalf 2) (by decide))
        (pointSub (run controlForce controlHalf controlState 2).1 controlState.1)) controlState.2)
      (Fraction.ofInt 0) := by unfold Fraction.le; decide

end NewtonLimitDynamics.Polygon.KinematicEstimates
