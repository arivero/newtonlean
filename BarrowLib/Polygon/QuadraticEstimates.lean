import BarrowLib.Polygon.AccelerationEstimates
import BarrowLib.Polygon.RationalIntervals

/-! Exact finite quadratic comparison for drift-then-kick iteration. The
constant-map position coefficient is t*(t-h)/2, rather than t²/2. Variable
maps have a derived cubic/error remainder; the remaining half-mesh bias is
explicit. No curve, derivative or integral is a premise. -/

namespace NewtonLimitDynamics.Polygon.QuadraticEstimates
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates BoundedIteration KinematicEstimates AccelerationEstimates
open HarmonicStability

def quadraticPosition (t : Fraction) (s : Point × Point) (a : Point) : Point :=
  pointAdd (pointAdd s.1 (pointScale t s.2)) (pointScale (Fraction.mul t t).half a)

theorem quadratic_time_congr (t u : Fraction) (s : Point × Point) (a : Point)
    (he : Fraction.equiv t u) : pointEquiv (quadraticPosition t s a) (quadraticPosition u s a) :=
  pointAdd_congr (pointAdd_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
    (pointScale_ratio_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩))
    (pointScale_ratio_congr ((show Fraction.equiv (Fraction.half _) (Fraction.half _) from by
        apply (Fraction.equiv_iff_toRat _ _).mpr
        simp only [Fraction.toRat_half]
        exact congrArg (fun q : Rat => q / 2) ((Fraction.equiv_iff_toRat _ _).mp (Fraction.mul_equiv he he))))
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)

def discreteWeight (h : Fraction) (n : Nat) : Fraction :=
  (Fraction.mul (time h n) (Fraction.add (time h n) (negF h))).half

def discretePosition (h : Fraction) (s : Point × Point) (a : Point) (n : Nat) : Point :=
  pointAdd (inertialPosition h s n) (pointScale (discreteWeight h n) a)

theorem discrete_zero (h : Fraction) (s : Point × Point) (a : Point) :
    pointEquiv (discretePosition h s a 0) s.1 := by
  constructor <;>
    simp only [discretePosition,discreteWeight,inertialPosition,time,pointEquiv,
      pointAdd,pointScale,negF,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,
      Fraction.ofInt,Int.natCast_zero,Int.zero_mul,Int.mul_zero,Int.add_zero] <;> ac_nf

theorem discrete_step (h : Fraction) (s : Point × Point) (a : Point) (n : Nat) :
    pointEquiv (discretePosition h s a (n+1))
      (pointAdd (discretePosition h s a n) (pointScale h (inertialPosition h (s.2,a) n))) := by
  constructor <;>
    simp only [discretePosition,discreteWeight,inertialPosition,time,pointEquiv,
      pointAdd,pointScale,negF,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,
      Fraction.ofInt,Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,
      Int.neg_mul,Int.mul_neg] <;>
    simp only [show (2 : Int)=1+1 by rfl,Int.add_mul,Int.mul_add] <;> ac_nf <;> omega

/-- The actual constant-map run, at every finite count. -/
theorem constant_run_formula (a : Point) (h : Fraction) (s : Point × Point) (n : Nat) :
    stateEquiv (run (fun _ => a) h s n)
      (discretePosition h s a n,inertialPosition h (s.2,a) n) := by
  induction n with
  | zero => exact ⟨pointEquiv_symm (discrete_zero h s a),pointEquiv_symm (inertial_zero h (s.2,a))⟩
  | succ n ih =>
    constructor
    · exact pointEquiv_trans (pointAdd_congr ih.1 (pointScale_congr h ih.2))
        (pointEquiv_symm (discrete_step h s a n))
    · exact pointEquiv_trans (pointAdd_congr ih.2
        (pointScale_congr h ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩))
        (pointEquiv_symm (inertial_step h (s.2,a) n))

/-- Sum the actual velocity remainders against the exact discrete quadratic
position, using the shared finite quadratic budget step. -/
theorem position_remainder_from_samples (a : Point → Point) (h : Fraction)
    (s : Point × Point) (C : Fraction) (hh : 0 ≤ h.num) (hC : 0 ≤ C.num) (N : Nat)
    (hs : ∀ i, i<N → Fraction.le (pointDistance (a (run a h s (i+1)).1) (a s.1)) C) :
    ∀ n, n≤N → Fraction.le (pointDistance (run a h s n).1 (discretePosition h s (a s.1) n))
      (Fraction.mul (Fraction.mul (time h n) (time h n)) C) := by
  intro n hn
  induction n with
  | zero =>
    apply Fraction.le_of_equiv
    apply Fraction.equiv_trans (pointDistance_equiv
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (discrete_zero h s (a s.1)))
    apply Fraction.equiv_trans (pointDistance_self_zero s.1)
    simp [time,Fraction.equiv,Fraction.mul,Fraction.ofInt]
  | succ n ih =>
    have hv := velocity_remainder_from_samples a h s C hh N hs n (by omega)
    have hs' := Fraction.le_equiv_left (difference_scale h _ _)
      (Fraction.le_equiv_right
        (Fraction.mul_le_mul_nonnegative_left hv h.abs (Fraction.abs_num_nonnegative h))
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl _)))
    have ha := difference_add_bound (run a h s n).1 (discretePosition h s (a s.1) n)
      (pointScale h (run a h s n).2) (pointScale h (predictedVelocity a h s n))
    have hb := Fraction.magnitudes.le_trans ha (Fraction.add_le_add (ih (by omega)) hs')
    have hc := Fraction.le_equiv_left
      (pointDistance_equiv (p := (run a h s (n+1)).1)
        ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (discrete_step h s (a s.1) n)) hb
    exact Fraction.magnitudes.le_trans hc (quadratic_step h C hh hC n)

theorem position_remainder_at (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hV : 0 ≤ V.num)
    (n : Nat)
    (hc : ∀ k, k<n → Fraction.le
      (pointDistance (a (run a h s (k+1)).1) (a s.1))
      (Fraction.add (Fraction.mul L (pointDistance (run a h s (k+1)).1 s.1)) E))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (run a h s n).1 (discretePosition h s (a s.1) n))
      (Fraction.mul (Fraction.mul (time h n) (time h n)) (source L E (time h n) V)) :=
  position_remainder_from_samples a h s _ hh
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _ hL (Fraction.nonnegative_mul _ _ (time_nonnegative h hh n) hV)) hE)
    n (fun i hi => force_variation_at a h s L E V hh hL hV n i hi (hc i hi) hv) n (Nat.le_refl _)


theorem position_remainder (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hV : 0 ≤ V.num)
    (hc : comparisonContract a a L E) (n : Nat)
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (run a h s n).1 (discretePosition h s (a s.1) n))
      (Fraction.mul (Fraction.mul (time h n) (time h n)) (source L E (time h n) V)) :=
  position_remainder_at a h s L E V hh hL hE hV n (fun _ _ => hc _ _) hv

theorem discrete_quadratic_offset (h : Fraction) (s : Point × Point) (a : Point) (n : Nat) :
    pointEquiv (pointSub (quadraticPosition (time h n) s a) (discretePosition h s a n))
      (pointScale (Fraction.mul (time h n) h).half a) := by
  constructor <;>
    simp only [quadraticPosition,discretePosition,discreteWeight,inertialPosition,
      pointEquiv,pointSub,pointNeg,pointAdd,pointScale,negF,Fraction.equiv,
      Fraction.add,Fraction.mul,Fraction.half,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;>
    ac_nf <;> omega

theorem half_mesh_bias (h : Fraction) (s : Point × Point) (a : Point)
    (hh : 0 ≤ h.num) (n : Nat) :
    Fraction.equiv (pointDistance (discretePosition h s a n) (quadraticPosition (time h n) s a))
      (Fraction.mul (Fraction.mul (time h n) h).half (pointNorm a)) := by
  have hr : 0 ≤ (Fraction.mul (time h n) h).half.num :=
    Fraction.nonnegative_mul _ _ (time_nonnegative h hh n) hh
  exact Fraction.equiv_trans (pointDistance_symm _ _)
    (Fraction.equiv_trans (pointNorm_equiv (discrete_quadratic_offset h s a n))
      (Fraction.equiv_trans (pointNorm_scale _ _)
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative _ hr) (Fraction.equiv_refl _))))

/-- Cubic force-variation remainder plus the explicit half-mesh bias. -/
theorem position_quadratic_remainder_at (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hV : 0 ≤ V.num)
    (n : Nat)
    (hc : ∀ k, k<n → Fraction.le
      (pointDistance (a (run a h s (k+1)).1) (a s.1))
      (Fraction.add (Fraction.mul L (pointDistance (run a h s (k+1)).1 s.1)) E))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (run a h s n).1 (quadraticPosition (time h n) s (a s.1)))
      (Fraction.add
        (Fraction.mul (Fraction.mul (time h n) (time h n)) (source L E (time h n) V))
        (Fraction.mul (Fraction.mul (time h n) h).half (pointNorm (a s.1)))) :=
  Fraction.magnitudes.le_trans (pointDistance_triangle _ (discretePosition h s (a s.1) n) _)
    (Fraction.add_le_add (position_remainder_at a h s L E V hh hL hE hV n hc hv)
      (Fraction.le_of_equiv (half_mesh_bias h s (a s.1) hh n)))


theorem position_quadratic_remainder (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hV : 0 ≤ V.num)
    (hc : comparisonContract a a L E) (n : Nat)
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (run a h s n).1 (quadraticPosition (time h n) s (a s.1)))
      (Fraction.add
        (Fraction.mul (Fraction.mul (time h n) (time h n)) (source L E (time h n) V))
        (Fraction.mul (Fraction.mul (time h n) h).half (pointNorm (a s.1)))) :=
  position_quadratic_remainder_at a h s L E V hh hL hE hV n (fun _ _ => hc _ _) hv

private def controlHalf : Fraction := ⟨1,2,by decide⟩
private def controlState : Point × Point :=
  ((Fraction.ofInt 0,Fraction.ofInt 0),(Fraction.ofInt 1,Fraction.ofInt 0))
private def controlForce : Point := (Fraction.ofInt 0,Fraction.ofInt (-1))

theorem two_cell_half_mesh_control :
    Fraction.equiv (pointDistance (run (fun _ => controlForce) controlHalf controlState 2).1
      (quadraticPosition (time controlHalf 2) controlState controlForce)) ⟨1,4,by decide⟩ := by decide

theorem exact_quadratic_rejects_finite_control :
    ¬ pointEquiv (run (fun _ => controlForce) controlHalf controlState 2).1
      (quadraticPosition (time controlHalf 2) controlState controlForce) := by decide

end NewtonLimitDynamics.Polygon.QuadraticEstimates
