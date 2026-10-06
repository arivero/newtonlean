import BarrowLib.Polygon.TriangleBounds
import BarrowLib.Polygon.FiniteEstimates
import BarrowLib.Polygon.DyadicArithmetic

/-! Finite rational determinant fans. Signed sums retain cancellation;
unsigned sums count each determinant with multiplicity. -/

namespace NewtonLimitDynamics.Polygon.PolygonFanArea
open NewtonLimitDynamics
open TimeSubdivision
open PointBounds FiniteEstimates TriangleBounds HarmonicTimeComparison

def neg (x : Fraction) : Fraction := ⟨-x.num,x.den,x.den_pos⟩
def sub (x y : Fraction) : Fraction := Fraction.add x (neg y)

def sum (a : Nat → Fraction) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | n+1 => Fraction.add (sum a n) (a n)

def fan (p : Nat → Point) (n : Nat) : Fraction :=
  sum (fun i => det (p i) (p (i+1))) n

def unsignedFan (p : Nat → Point) (n : Nat) : Fraction :=
  sum (fun i => (det (p i) (p (i+1))).abs) n

/-- Cells starting at `lo`, with a count independent of the initial prefix. -/
def intervalSum (a : Nat → Fraction) (lo count : Nat) : Fraction :=
  sum (fun i => a (lo+i)) count

def intervalFan (unsigned : Bool) (p : Nat → Point) (lo count : Nat) : Fraction :=
  intervalSum (fun i => if unsigned then (det (p i) (p (i+1))).abs
    else det (p i) (p (i+1))) lo count

theorem intervalSum_compose (a : Nat → Fraction) (lo n k : Nat) :
    Fraction.equiv (intervalSum a lo (n+k))
      (Fraction.add (intervalSum a lo n) (intervalSum a (lo+n) k)) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, intervalSum, sum]
    simp only [Fraction.equiv,Fraction.add,Fraction.ofInt]
    simp only [Int.zero_mul,Int.add_zero,Int.mul_one]
  | succ k ih =>
    have h := Fraction.add_equiv ih (Fraction.equiv_refl (a (lo+(n+k))))
    have hassoc : Fraction.equiv
        (Fraction.add (Fraction.add (intervalSum a lo n) (intervalSum a (lo+n) k))
          (a (lo+(n+k))))
        (Fraction.add (intervalSum a lo n)
          (Fraction.add (intervalSum a (lo+n) k) (a ((lo+n)+k)))) := by
      simp only [Fraction.equiv,Fraction.add]
      simp only [Int.add_mul,Int.mul_add]
      ac_nf
    simpa only [intervalSum, sum, Nat.add_succ, Nat.add_assoc] using
      Fraction.equiv_trans h hassoc

theorem intervalFan_compose (unsigned : Bool) (p : Nat → Point) (lo n k : Nat) :
    Fraction.equiv (intervalFan unsigned p lo (n+k))
      (Fraction.add (intervalFan unsigned p lo n)
        (intervalFan unsigned p (lo+n) k)) :=
  intervalSum_compose _ lo n k

theorem det_congr {p p' q q' : Point}
    (hp : pointEquiv p p') (hq : pointEquiv q q') :
    Fraction.equiv (det p q) (det p' q') :=
  TimeSubdivision.det_congr hp hq

theorem sub_add (a b c d : Fraction) :
    Fraction.equiv (sub (Fraction.add a c) (Fraction.add b d))
      (Fraction.add (sub a b) (sub c d)) := by
  simp only [sub,neg,Fraction.equiv,Fraction.add,Int.add_mul,Int.mul_add,
    Int.neg_mul,Int.mul_neg]
  ac_nf <;> omega

theorem abs_sub_abs_le (a b : Fraction) :
    Fraction.le (sub a.abs b.abs).abs (sub a b).abs := by
  let A := a.num * b.den
  let B := b.num * a.den
  have h1 := Int.natAbs_sub_le (A-B) (-B)
  have h2 := Int.natAbs_sub_le (B-A) (-A)
  have hs : (Int.natAbs ((Int.natAbs A : Int) - Int.natAbs B) : Int) ≤
      Int.natAbs (A-B) := by
    have hne : Int.natAbs (B-A) = Int.natAbs (A-B) := by
      rw [show B-A= -(A-B) by omega,Int.natAbs_neg]
    simp only [Int.sub_neg] at h1 h2
    rw [Int.sub_add_cancel] at h1 h2
    simp only [Int.natAbs_neg] at h1 h2
    omega
  unfold Fraction.le sub neg Fraction.add Fraction.abs
  dsimp
  have hden : 0 ≤ a.den * b.den := Int.le_of_lt (Int.mul_pos a.den_pos b.den_pos)
  have hnum : (Int.natAbs ((Int.natAbs A : Int) - Int.natAbs B) : Int) ≤
      Int.natAbs (A-B) := hs
  have hm := Int.mul_le_mul_of_nonneg_right hnum hden
  simpa only [A,B,Int.natAbs_mul,Int.ofNat_mul,Int.neg_mul,
    Int.natAbs_of_nonneg (Int.le_of_lt a.den_pos),
    Int.natAbs_of_nonneg (Int.le_of_lt b.den_pos),Int.sub_eq_add_neg] using hm

theorem duration_abs_reverse (a b : Fraction) :
    Fraction.le (durationDifference a.abs b.abs).abs
      (durationDifference a b).abs := abs_sub_abs_le b a

theorem det_inertial_remainder (p v q : Point) (h : Fraction) :
    Fraction.equiv
      (durationDifference (Fraction.mul h (det p v)) (det p q))
      (det p (pointSub q (pointAdd p (pointScale h v)))) := by
  simp only [durationDifference,HarmonicStability.negF,det,pointSub,pointAdd,
    pointScale,pointNeg,Fraction.equiv,Fraction.add,Fraction.mul,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
  ac_nf <;> omega

theorem det_inertial_remainder_bound (p v q : Point) (h R e : Fraction)
    (hp : Fraction.le (pointNorm p) R)
    (he : Fraction.le (pointDistance q (pointAdd p (pointScale h v))) e) :
    Fraction.le
      (durationDifference (Fraction.mul h (det p v)) (det p q)).abs
      (Fraction.mul R e) := by
  have hdet := det_abs_le_product p (pointSub q (pointAdd p (pointScale h v)))
  have hmul := Fraction.mul_le_mul_nonnegative_left he (pointNorm p)
    (pointNorm_nonnegative p)
  have he_nonnegative : 0 ≤ e.num := by
    have hn := pointNorm_nonnegative (pointSub q (pointAdd p (pointScale h v)))
    have hl : 0 ≤ (pointDistance q (pointAdd p (pointScale h v))).num * e.den :=
      Int.mul_nonneg hn (Int.le_of_lt e.den_pos)
    have hr : 0 ≤ e.num * (pointDistance q (pointAdd p (pointScale h v))).den :=
      Int.le_trans hl he
    by_cases hneg : 0 ≤ e.num
    · exact hneg
    · have hneg' : 0 < -e.num := by omega
      have hp' := Int.mul_pos hneg'
        (pointDistance q (pointAdd p (pointScale h v))).den_pos
      simp only [Int.neg_mul] at hp'
      omega
  have hRmul := Fraction.mul_le_mul_nonnegative hp e he_nonnegative
  exact Fraction.le_equiv_left (Fraction.abs_equiv (det_inertial_remainder p v q h))
    (Fraction.magnitudes.le_trans hdet (Fraction.magnitudes.le_trans hmul hRmul))

theorem sum_congr (a b : Nat → Fraction)
    (h : ∀ i, Fraction.equiv (a i) (b i)) :
    ∀ n, Fraction.equiv (sum a n) (sum b n)
  | 0 => Fraction.equiv_refl _
  | n+1 => Fraction.add_equiv (sum_congr a b h n) (h n)

theorem fan_congr {p q : Nat → Point}
    (h : ∀ i, pointEquiv (p i) (q i)) (n : Nat) :
    Fraction.equiv (fan p n) (fan q n) :=
  sum_congr _ _ (fun i => det_congr (h i) (h (i+1))) n

theorem unsignedFan_congr {p q : Nat → Point}
    (h : ∀ i, pointEquiv (p i) (q i)) (n : Nat) :
    Fraction.equiv (unsignedFan p n) (unsignedFan q n) :=
  sum_congr _ _ (fun i => Fraction.abs_equiv (det_congr (h i) (h (i+1)))) n

theorem sum_difference (a b : Nat → Fraction) : ∀ n,
    Fraction.equiv (sub (sum a n) (sum b n)) (sum (fun i => sub (a i) (b i)) n)
  | 0 => by
      simp only [sum,sub,neg,Fraction.equiv,Fraction.add,Fraction.ofInt,
        Int.zero_mul,Int.mul_zero,Int.neg_zero,Int.add_zero,Int.zero_add,
        Int.one_mul,Int.mul_one]
  | n+1 => Fraction.equiv_trans (sub_add _ _ _ _)
      (Fraction.add_equiv (sum_difference a b n) (Fraction.equiv_refl _))

theorem sum_abs_le (a : Nat → Fraction) : ∀ n,
    Fraction.le (sum a n).abs (sum (fun i => (a i).abs) n)
  | 0 => by
      simp only [sum,Fraction.abs,Fraction.le,Fraction.ofInt,Int.natAbs_zero,
        Int.natCast_zero,Int.zero_mul]
      omega
  | n+1 => Fraction.magnitudes.le_trans (Fraction.abs_add_le _ _)
      (Fraction.add_le_add (sum_abs_le a n) (Fraction.le_of_equiv (Fraction.equiv_refl _)))

theorem sum_mono (a b : Nat → Fraction) (n : Nat)
    (h : ∀ i, i<n → Fraction.le (a i) (b i)) :
    Fraction.le (sum a n) (sum b n) := by
  induction n with
  | zero => exact Fraction.le_of_equiv (Fraction.equiv_refl _)
  | succ n ih => exact Fraction.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem sum_constant (e : Fraction) : ∀ n,
    Fraction.equiv (sum (fun _ => e) n) (Fraction.mul (Fraction.ofInt n) e)
  | 0 => by
      simp only [sum,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_zero,
        Int.zero_mul,Int.mul_one]
  | n+1 => by
      have ih := sum_constant e n
      apply Fraction.equiv_trans (Fraction.add_equiv ih (Fraction.equiv_refl _))
      simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
        Int.natCast_add,Int.natCast_one,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
      ac_nf

theorem sum_error (a b : Nat → Fraction) (e : Fraction) (n : Nat)
    (h : ∀ i, i<n → Fraction.le (sub (a i) (b i)).abs e) :
    Fraction.le (sub (sum a n) (sum b n)).abs
      (Fraction.mul (Fraction.ofInt n) e) :=
  Fraction.le_equiv_right
    (Fraction.magnitudes.le_trans
      (Fraction.le_equiv_left (Fraction.abs_equiv (sum_difference a b n))
        (sum_abs_le (fun i => sub (a i) (b i)) n))
      (sum_mono _ _ n h))
    (sum_constant e n)

theorem intervalSum_error (a b : Nat → Fraction) (lo count : Nat) (e : Fraction)
    (h : ∀ i, i<count → Fraction.le (sub (a (lo+i)) (b (lo+i))).abs e) :
    Fraction.le (sub (intervalSum a lo count) (intervalSum b lo count)).abs
      (Fraction.mul (Fraction.ofInt count) e) :=
  sum_error (fun i => a (lo+i)) (fun i => b (lo+i)) e count h

theorem fan_error (p q : Nat → Point) (e : Fraction) (n : Nat)
    (h : ∀ i, i<n → Fraction.le
      (sub (det (p i) (p (i+1))) (det (q i) (q (i+1)))).abs e) :
    Fraction.le (sub (fan p n) (fan q n)).abs
      (Fraction.mul (Fraction.ofInt n) e) := sum_error _ _ e n h

theorem unsignedFan_error (p q : Nat → Point) (e : Fraction) (n : Nat)
    (h : ∀ i, i<n → Fraction.le
      (sub (det (p i) (p (i+1))) (det (q i) (q (i+1)))).abs e) :
    Fraction.le (sub (unsignedFan p n) (unsignedFan q n)).abs
      (Fraction.mul (Fraction.ofInt n) e) :=
  sum_error _ _ e n (fun i hi => Fraction.magnitudes.le_trans (abs_sub_abs_le _ _) (h i hi))

end NewtonLimitDynamics.Polygon.PolygonFanArea
