import BarrowLib.Polygon.QuadraticEstimates
import ModernLib.Foundation.Polygon.SecantValues

/-! Normalized second-order position departure, composed from the existing
proved secant operators. Actual finite quadratic remainders yield force error
2*(L*t*V+E)+(h/t)*|a(x0)|. The half-mesh bias remains explicit. -/

namespace NewtonLimitDynamics.Polygon.QuadraticSecants
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates BoundedIteration KinematicEstimates
open AccelerationEstimates QuadraticEstimates SecantValues CauchyValues

def secondState (t : Fraction) (ht : 0 < t.num) (s u : Point × Point) : Point × Point :=
  secantState (Fraction.mul (Fraction.ofInt 2) (TimeCalibration.inverse t ht))
    (secantState (TimeCalibration.inverse t ht) u s) (velocityState s)

def secondValue (t : Fraction) (ht : 0 < t.num) (x y : Value) : Value :=
  secantValue (Fraction.mul (Fraction.ofInt 2) (TimeCalibration.inverse t ht))
    (secantValue (TimeCalibration.inverse t ht) y x) (velocityValue x)

theorem second_identity (t : Fraction) (ht : 0 < t.num) (s u : Point × Point) (a : Point) :
    pointEquiv (pointSub (secondState t ht s u).1 a)
      (pointScale (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (TimeCalibration.inverse t ht) (TimeCalibration.inverse t ht)))
        (pointSub u.1 (quadraticPosition t s a))) := by
  constructor <;>
    simp only [secondState,secantState,pointState,velocityState,quadraticPosition,
      TimeCalibration.inverse,pointEquiv,pointSub,pointNeg,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,Fraction.ofInt,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one] <;>
    ac_nf <;> omega

theorem second_state_time_congr (t u : Fraction) (ht : 0 < t.num) (hu : 0 < u.num)
    (he : Fraction.equiv t u) (s v : Point × Point) :
    pointEquiv (secondState t ht s v).1 (secondState u hu s v).1 := by
  have hi := TimeCalibration.inverse_congr ht hu he
  have h1 := pointScale_ratio_congr hi
    (show pointEquiv (pointSub v.1 s.1) (pointSub v.1 s.1) from
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
  have hd := pointSub_congr h1
    (show pointEquiv s.2 s.2 from ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
  exact pointScale_ratio_congr (Fraction.mul_equiv (Fraction.equiv_refl _) hi) hd

theorem finite_second_bound_at (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hV : 0 ≤ V.num)
    (n : Nat) (ht : 0 < (time h n).num)
    (hc : ∀ k, k<n → Fraction.le
      (pointDistance (a (run a h s (k+1)).1) (a s.1))
      (Fraction.add (Fraction.mul L (pointDistance (run a h s (k+1)).1 s.1)) E))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (secondState (time h n) ht s (run a h s n)).1 (a s.1))
      (Fraction.add (Fraction.mul (Fraction.ofInt 2) (source L E (time h n) V))
        (Fraction.mul (Fraction.mul h (TimeCalibration.inverse (time h n) ht)) (pointNorm (a s.1)))) := by
  let q := Fraction.mul (Fraction.ofInt 2)
    (Fraction.mul (TimeCalibration.inverse (time h n) ht) (TimeCalibration.inverse (time h n) ht))
  have hq : 0 ≤ q.num := Fraction.nonnegative_mul _ _ (by decide)
    (Fraction.nonnegative_mul _ _ (Int.le_of_lt (time h n).den_pos) (Int.le_of_lt (time h n).den_pos))
  have he := Fraction.equiv_trans (pointNorm_equiv (second_identity (time h n) ht s (run a h s n) (a s.1)))
    (pointNorm_scale q _)
  have hb := Fraction.mul_le_mul_nonnegative_left
    (position_quadratic_remainder_at a h s L E V hh hL hE hV n hc hv) q hq
  have he' := Fraction.equiv_trans he
    (Fraction.mul_equiv (Fraction.abs_of_nonnegative q hq) (Fraction.equiv_refl _))
  apply Fraction.le_equiv_right (Fraction.le_equiv_left he' hb)
  simp only [q,TimeCalibration.inverse,Fraction.equiv,Fraction.mul,Fraction.add,Fraction.half,Fraction.ofInt,
    Int.add_mul,Int.mul_add]
  ac_nf


theorem finite_second_bound (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hV : 0 ≤ V.num)
    (hc : comparisonContract a a L E) (n : Nat) (ht : 0 < (time h n).num)
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (secondState (time h n) ht s (run a h s n)).1 (a s.1))
      (Fraction.add (Fraction.mul (Fraction.ofInt 2) (source L E (time h n) V))
        (Fraction.mul (Fraction.mul h (TimeCalibration.inverse (time h n) ht)) (pointNorm (a s.1)))) :=
  finite_second_bound_at a h s L E V hh hL hE hV n ht (fun _ _ => hc _ _) hv

theorem finite_second_equivalent_time_at (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V u : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hV : 0 ≤ V.num)
    (n : Nat) (ht : 0 < (time h n).num)
    (hc : ∀ k, k<n → Fraction.le
      (pointDistance (a (run a h s (k+1)).1) (a s.1))
      (Fraction.add (Fraction.mul L (pointDistance (run a h s (k+1)).1 s.1)) E)) (hu : 0 < u.num)
    (he : Fraction.equiv u (time h n))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (secondState u hu s (run a h s n)).1 (a s.1))
      (Fraction.add (Fraction.mul (Fraction.ofInt 2) (source L E u V))
        (Fraction.mul (Fraction.mul h (TimeCalibration.inverse u hu)) (pointNorm (a s.1)))) := by
  apply Fraction.le_equiv_right
    (Fraction.le_equiv_left (pointDistance_equiv (second_state_time_congr u (time h n) hu ht he s _)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (finite_second_bound_at a h s L E V hh hL hE hV n ht hc hv))
  exact Fraction.add_equiv
    (Fraction.mul_equiv (Fraction.equiv_refl _) (Fraction.add_equiv
      (Fraction.mul_equiv (Fraction.equiv_refl L) (Fraction.mul_equiv (Fraction.equiv_symm he)
        (Fraction.equiv_refl V))) (Fraction.equiv_refl E)))
    (Fraction.mul_equiv (Fraction.mul_equiv (Fraction.equiv_refl h)
      (TimeCalibration.inverse_congr ht hu (Fraction.equiv_symm he))) (Fraction.equiv_refl _))


theorem finite_second_equivalent_time (a : Point → Point) (h : Fraction) (s : Point × Point)
    (L E V u : Fraction) (hh : 0 ≤ h.num) (hL : 0 ≤ L.num) (hE : 0 ≤ E.num) (hV : 0 ≤ V.num)
    (hc : comparisonContract a a L E) (n : Nat) (ht : 0 < (time h n).num) (hu : 0 < u.num)
    (he : Fraction.equiv u (time h n))
    (hv : ∀ k, k<n → Fraction.le (pointNorm (run a h s k).2) V) :
    Fraction.le (pointDistance (secondState u hu s (run a h s n)).1 (a s.1))
      (Fraction.add (Fraction.mul (Fraction.ofInt 2) (source L E u V))
        (Fraction.mul (Fraction.mul h (TimeCalibration.inverse u hu)) (pointNorm (a s.1)))) :=
  finite_second_equivalent_time_at a h s L E V u hh hL hE hV n ht (fun _ _ => hc _ _) hu he hv

end NewtonLimitDynamics.Polygon.QuadraticSecants
