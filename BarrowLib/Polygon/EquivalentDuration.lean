import BarrowLib.Polygon.ConvexCover
import BarrowLib.Polygon.TimeCalibration

/-! Actual triangular cells at value-equivalent rational durations. A sampled
map may distinguish point representatives; comparison retains its additive E. -/

namespace NewtonLimitDynamics.Polygon.EquivalentDuration

open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates ConvexCover

theorem pointDistance_zero_of_equiv {p q : Point} (hpq : pointEquiv p q) :
    Fraction.equiv (pointDistance p q) (Fraction.ofInt 0) := by
  have he : pointEquiv (pointSub p q) (pointSub p p) :=
    pointSub_congr ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩
      (pointEquiv_symm hpq)
  exact Fraction.equiv_trans (pointNorm_equiv he) (pointSub_self_zero p)

theorem cell_position_equiv {d e : Fraction} (a : Point → Point)
    (s : Point × Point) (hde : Fraction.equiv d e) :
    pointEquiv (cell a d s).1 (cell a e s).1 :=
  pointAdd_congr ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩
    (pointScale_ratio_congr hde
      ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩)

theorem cell_position_perturbation (a b : Point → Point) (d e : Fraction)
    (s t : Point × Point) (hde : Fraction.equiv d e) :
    Fraction.le (pointDistance (cell a d s).1 (cell b e t).1)
      (Fraction.add (pointDistance s.1 t.1)
        (Fraction.mul d.abs (pointDistance s.2 t.2))) := by
  have hpos := cell_position_equiv b t (Fraction.equiv_symm hde)
  exact Fraction.le_equiv_left
    (pointDistance_equiv ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ hpos)
    (FiniteEstimates.cell_position_perturbation a b d s t)

theorem cell_velocity_perturbation_at (a b : Point → Point) (d e L E : Fraction)
    (s t : Point × Point) (hde : Fraction.equiv d e)
    (hc : Fraction.le (pointDistance (a (cell a d s).1) (b (cell b e t).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (cell a d s).1 (cell b e t).1)) E)) :
    Fraction.le (pointDistance (cell a d s).2 (cell b e t).2)
      (Fraction.add (pointDistance s.2 t.2)
        (Fraction.mul d.abs
          (Fraction.add (Fraction.mul L
            (pointDistance (cell a d s).1 (cell b e t).1)) E))) := by
  let A := a (cell a d s).1
  let B := b (cell b e t).1
  have hs : pointEquiv (pointScale e B) (pointScale d B) :=
    pointScale_ratio_congr (Fraction.equiv_symm hde)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  have hv : pointEquiv (cell b e t).2 (pointAdd t.2 (pointScale d B)) :=
    pointAdd_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ hs
  have hb := difference_add_bound s.2 t.2 (pointScale d A) (pointScale d B)
  have hm := Fraction.mul_le_mul_nonnegative_left
    hc d.abs (Fraction.abs_num_nonnegative d)
  have hscaled := Fraction.le_equiv_right hb
    (Fraction.add_equiv (Fraction.equiv_refl _) (difference_scale d A B))
  exact Fraction.le_equiv_left
    (pointDistance_equiv ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ hv)
    (Fraction.magnitudes.le_trans hscaled (Fraction.add_le_add_left hm _))

theorem cell_velocity_perturbation (a b : Point → Point) (d e L E : Fraction)
    (s t : Point × Point) (hde : Fraction.equiv d e)
    (hc : comparisonContract a b L E) :
    Fraction.le (pointDistance (cell a d s).2 (cell b e t).2)
      (Fraction.add (pointDistance s.2 t.2)
        (Fraction.mul d.abs
          (Fraction.add (Fraction.mul L
            (pointDistance (cell a d s).1 (cell b e t).1)) E))) :=
  cell_velocity_perturbation_at a b d e L E s t hde
    (hc (cell a d s).1 (cell b e t).1)

/-- Both forces remain evaluated at the actual arrivals of their own duration. -/
theorem cell_amplification_at (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (d e L E : Fraction) (s t : Point × Point)
    (hde : Fraction.equiv d e) (hL : 0 ≤ L.num)
    (hc : Fraction.le (pointDistance (a (cell a d s).1) (b (cell b e t).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (cell a d s).1 (cell b e t).1)) E)) :
    Fraction.le (TimeCalibration.distance tau (cell a d s) (cell b e t))
      (Fraction.add
        (Fraction.mul (TimeCalibration.amplification tau d L ht)
          (TimeCalibration.distance tau s t))
        (Fraction.mul (Fraction.mul tau d.abs) E)) := by
  have hp := cell_position_perturbation a b d e s t hde
  have hv := cell_velocity_perturbation_at a b d e L E s t hde hc
  have hvc := Fraction.magnitudes.le_trans hv
    (Fraction.add_le_add_left
      (Fraction.mul_le_mul_nonnegative_left
        (Fraction.add_le_add_right
          (Fraction.mul_le_mul_nonnegative_left hp L hL) E)
        d.abs (Fraction.abs_num_nonnegative d)) (pointDistance s.2 t.2))
  have hsum := Fraction.add_le_add hp
    (Fraction.mul_le_mul_nonnegative_left hvc tau (Int.le_of_lt ht))
  have hcomp := TimeCalibration.component_amplification tau (pointDistance s.1 t.1)
    (pointDistance s.2 t.2) d.abs L E ht
    (pointNorm_nonnegative _) (pointNorm_nonnegative _) (Fraction.abs_num_nonnegative d) hL
  have hh : d.abs.abs = d.abs := by simp only [Fraction.abs,Int.natAbs_natCast]
  simpa only [TimeCalibration.distance,TimeCalibration.amplification,hh] using!
    Fraction.magnitudes.le_trans hsum hcomp

theorem cell_amplification (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (d e L E : Fraction) (s t : Point × Point)
    (hde : Fraction.equiv d e) (hL : 0 ≤ L.num)
    (hc : comparisonContract a b L E) :
    Fraction.le (TimeCalibration.distance tau (cell a d s) (cell b e t))
      (Fraction.add
        (Fraction.mul (TimeCalibration.amplification tau d L ht)
          (TimeCalibration.distance tau s t))
        (Fraction.mul (Fraction.mul tau d.abs) E)) :=
  cell_amplification_at tau ht a b d e L E s t hde hL
    (hc (cell a d s).1 (cell b e t).1)

theorem run_distance_le_source_at (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (d e L E : Fraction) (s : Point × Point)
    (hde : Fraction.equiv d e) (hL : 0 ≤ L.num) :
    (n : Nat) →
    (hc : ∀ k, k < n → Fraction.le
      (pointDistance
        (a (cell a d (BoundedIteration.run a d s k)).1)
        (b (cell b e (BoundedIteration.run b e s k)).1))
      (Fraction.add (Fraction.mul L
        (pointDistance
          (cell a d (BoundedIteration.run a d s k)).1
          (cell b e (BoundedIteration.run b e s k)).1)) E)) →
    Fraction.le
      (TimeCalibration.distance tau (BoundedIteration.run a d s n) (BoundedIteration.run b e s n))
      (Fraction.ofRat (FiniteRecurrence.sourceBudget
        (TimeCalibration.amplification tau d L ht).toRat
        (Fraction.mul (Fraction.mul tau d.abs) E).toRat n))
  | 0, _ => Fraction.le_of_equiv (TimeCalibration.distance_self_zero tau s)
  | n+1, hc => by
      have hstep := cell_amplification_at tau ht a b d e L E
        (BoundedIteration.run a d s n) (BoundedIteration.run b e s n) hde hL
        (hc n (by omega))
      have hnext := Fraction.add_le_add_right
        (Fraction.mul_le_mul_nonnegative_left
          (run_distance_le_source_at tau ht a b d e L E s hde hL n
            (fun k hk => hc k (by omega)))
          (TimeCalibration.amplification tau d L ht)
          (TimeCalibration.amplification_nonnegative tau d L ht hL))
        (Fraction.mul (Fraction.mul tau d.abs) E)
      apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans hstep hnext)
      apply (Fraction.equiv_iff_toRat _ _).mpr
      simp only [Fraction.toRat_add, Fraction.toRat_mul, Fraction.toRat_ofRat,
        FiniteRecurrence.sourceBudget]

theorem run_distance_le_source (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (d e L E : Fraction) (s : Point × Point)
    (hde : Fraction.equiv d e) (hL : 0 ≤ L.num)
    (hc : comparisonContract a b L E) :
    (n : Nat) → Fraction.le
      (TimeCalibration.distance tau (BoundedIteration.run a d s n) (BoundedIteration.run b e s n))
      (Fraction.ofRat (FiniteRecurrence.sourceBudget
        (TimeCalibration.amplification tau d L ht).toRat
        (Fraction.mul (Fraction.mul tau d.abs) E).toRat n)) :=
  fun n => run_distance_le_source_at tau ht a b d e L E s hde hL n
    (fun k _ => hc
      (cell a d (BoundedIteration.run a d s k)).1
      (cell b e (BoundedIteration.run b e s k)).1)

theorem run_uniform_error_at (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (d e L E : Fraction) (s : Point × Point)
    (hde : Fraction.equiv d e) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (n : Nat)
    (hs : TimeCalibration.Window tau d L ht n)
    (hc : ∀ k, k < n → Fraction.le
      (pointDistance
        (a (cell a d (BoundedIteration.run a d s k)).1)
        (b (cell b e (BoundedIteration.run b e s k)).1))
      (Fraction.add (Fraction.mul L
        (pointDistance
          (cell a d (BoundedIteration.run a d s k)).1
          (cell b e (BoundedIteration.run b e s k)).1)) E)) :
    Fraction.le
      (TimeCalibration.distance tau (BoundedIteration.run a d s n) (BoundedIteration.run b e s n))
      (Fraction.mul (Fraction.ofInt (2*(n : Int)))
        (Fraction.mul (Fraction.mul tau d.abs) E)) := by
  let K := TimeCalibration.amplification tau d L ht
  let S := Fraction.mul (Fraction.mul tau d.abs) E
  have hK := TimeCalibration.amplification_nonnegative tau d L ht hL
  have hS : 0 ≤ S.num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt ht) (Fraction.abs_num_nonnegative d)) hE
  have hp := TimeCalibration.amplification_power_le_two tau d L ht hL n hs
  exact Fraction.magnitudes.le_trans
    (run_distance_le_source_at tau ht a b d e L E s hde hL n hc)
    (FiniteRecurrence.legacy_sourceBudget_two_count K S n hK hS
      (TimeCalibration.one_le_amplification tau d L ht hL) hp)

theorem run_uniform_error (tau : Fraction) (ht : 0 < tau.num)
    (a b : Point → Point) (d e L E : Fraction) (s : Point × Point)
    (hde : Fraction.equiv d e) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num)
    (hc : comparisonContract a b L E) (n : Nat)
    (hs : TimeCalibration.Window tau d L ht n) :
    Fraction.le
      (TimeCalibration.distance tau (BoundedIteration.run a d s n) (BoundedIteration.run b e s n))
      (Fraction.mul (Fraction.ofInt (2*(n : Int)))
        (Fraction.mul (Fraction.mul tau d.abs) E)) :=
  run_uniform_error_at tau ht a b d e L E s hde hL hE n hs
    (fun k _ => hc
      (cell a d (BoundedIteration.run a d s k)).1
      (cell b e (BoundedIteration.run b e s k)).1)

private def representativeMap (p : Point) : Point :=
  (Fraction.ofInt 0, if p.1.den = 1 then Fraction.ofInt 1 else Fraction.ofInt 2)
private def rest : Point × Point :=
  ((Fraction.ofInt 0,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0))

/-- Pure map control: equal duration values do not imply equal sample outputs. -/
theorem representative_sensitive_control :
    Fraction.equiv (Fraction.ofInt 1) (⟨2,2,by decide⟩ : Fraction) ∧
    Fraction.equiv
      (TimeCalibration.distance (Fraction.ofInt 2)
        (cell representativeMap (Fraction.ofInt 1) rest)
        (cell representativeMap ⟨2,2,by decide⟩ rest)) (Fraction.ofInt 2) ∧
    ¬ stateEquiv
      (cell representativeMap (Fraction.ofInt 1) rest)
      (cell representativeMap ⟨2,2,by decide⟩ rest) := by
  unfold stateEquiv
  decide

end NewtonLimitDynamics.Polygon.EquivalentDuration
