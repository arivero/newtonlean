import ModernLib.Foundation.Polygon.PositionValues
import ModernLib.Foundation.Polygon.BinaryTime
import ModernLib.Foundation.Polygon.ScaledTolerance
import BarrowLib.Polygon.ConvexCover

namespace NewtonLimitDynamics.Polygon.AffineValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds
open HarmonicComparison HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization
open BinaryTime CauchyValues PositionValues

def zeroPoint : Point := (Fraction.ofInt 0, Fraction.ofInt 0)
def affineState (x v : Point) (t : Fraction) : Point × Point :=
  (pointAdd x (pointScale t v), zeroPoint)

theorem affine_zero_phase (x v : Point) (t : Fraction) (ht : t.num = 0) :
    stateEquiv (affineState x v t) (x,zeroPoint) := by
  constructor
  · constructor <;> simp only [affineState, pointAdd, pointScale,
      Fraction.equiv, Fraction.add, Fraction.mul, ht, Int.zero_mul,
      Int.zero_add] <;> ac_nf
  · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

theorem affine_difference (x v : Point) (t u : Fraction) :
    stateEquiv (stateSub (affineState x v t) (affineState x v u))
      (pointScale (durationDifference u t) v, zeroPoint) := by
  constructor <;> constructor <;>
    simp only [affineState, stateSub, zeroPoint, pointEquiv, pointSub, pointNeg,
      pointAdd, pointScale, durationDifference, HarmonicStability.negF,
      Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

theorem affine_distance (x v : Point) (t u : Fraction) :
    Fraction.equiv (distance (affineState x v t) (affineState x v u))
      (Fraction.mul (durationDifference u t).abs (pointNorm v)) := by
  have he := stateNorm_equiv (affine_difference x v t u)
  have hz : pointNorm zeroPoint = Fraction.ofInt 0 := rfl
  apply Fraction.equiv_trans he
  change Fraction.equiv (Fraction.add (pointNorm (pointScale (durationDifference u t) v))
    (pointNorm zeroPoint)) _
  rw [hz]
  exact Fraction.equiv_trans (Fraction.add_zero _) (pointNorm_scale _ _)

theorem shift_difference (c t u : Fraction) :
    Fraction.equiv
      (durationDifference (durationDifference c u) (durationDifference c t))
      (durationDifference u t) := by
  simp only [durationDifference, HarmonicStability.negF, Fraction.equiv,
    Fraction.add, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

def edgeName (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (x v : Point) (m : Nat) : EndpointCauchyName where
  approx := fun j => affineState x v
    (durationDifference (timeApprox b T m) (timeApprox b T (m+j)))
  cauchy := by
    intro eps heps
    let V := pointNorm v
    let delta := factorDelta V eps (pointNorm_nonnegative v)
    have hdelta := factorDelta_positive V eps (pointNorm_nonnegative v) heps
    obtain ⟨N,hN⟩ := (BinaryTime.timeName b T hT).cauchy delta hdelta
    refine ⟨N, ?_⟩
    intro i j hi hj
    have ht := hN (m+i) (m+j) (by omega) (by omega)
    have hd := scalarState_distance (timeApprox b T (m+i)) (timeApprox b T (m+j))
    have hg := Fraction.magnitudes.lt_of_le_lt
      (Fraction.le_of_equiv (Fraction.equiv_symm hd)) ht
    have hc := factor_control V eps
      (durationDifference (timeApprox b T (m+j)) (timeApprox b T (m+i))).abs
      (pointNorm_nonnegative v) (Fraction.abs_num_nonnegative _) hg
    have ha := Fraction.equiv_trans
      (affine_distance x v
        (durationDifference (timeApprox b T m) (timeApprox b T (m+i)))
        (durationDifference (timeApprox b T m) (timeApprox b T (m+j))))
      (Fraction.mul_equiv (Fraction.abs_equiv (shift_difference _ _ _))
        (Fraction.equiv_refl (pointNorm v)))
    exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv ha) hc

theorem affine_vertex_distance (x v : Point) (t : Fraction) :
    Fraction.equiv (distance (affineState x v t) (x, zeroPoint))
      (Fraction.mul t.abs (pointNorm v)) := by
  have hp := ConvexCover.drift_offset t x v
  have he := Fraction.add_equiv (pointNorm_equiv hp)
    (ConvexCover.pointSub_self_zero zeroPoint)
  exact Fraction.equiv_trans he
    (Fraction.equiv_trans (Fraction.add_zero _) (pointNorm_scale t v))

/-- Every later binary-time approximant remains within one coarse duration
of its level-m starting time. -/
theorem phase_abs_bound (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m j : Nat) :
    Fraction.le (durationDifference (timeApprox b T m) (timeApprox b T (m+j))).abs
      (duration T m) :=
  Fraction.le_equiv_left
    (Fraction.equiv_symm (scalarState_distance _ _))
    (finite_gap_time b T hT j m)

theorem phase_nonnegative (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m : Nat) : (j : Nat) →
    0 ≤ (durationDifference (timeApprox b T m) (timeApprox b T (m+j))).num
  | 0 => by
      simp only [Nat.add_zero, durationDifference, HarmonicStability.negF, Fraction.add,
        Int.neg_mul]
      omega
  | j+1 => by
      have hp := phase_nonnegative b T hT m j
      have hs := Fraction.nonnegative_equiv (time_step_difference b T (m+j))
        (Fraction.nonnegative_mul _ _ (Int.ofNat_nonneg _) hT)
      have hc := durationDifference_chain (timeApprox b T m)
        (timeApprox b T (m+j)) (timeApprox b T (m+(j+1)))
      exact Fraction.nonnegative_equiv hc (Fraction.nonnegative_add _ _ hp
        (by simpa only [Nat.add_assoc] using hs))

/-- The time phase is between the two boundaries of the actual coarse cell. -/
theorem phase_interval (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m j : Nat) :
    0 ≤ (durationDifference (timeApprox b T m) (timeApprox b T (m+j))).num ∧
    Fraction.le (durationDifference (timeApprox b T m) (timeApprox b T (m+j)))
      (duration T m) := by
  have hn := phase_nonnegative b T hT m j
  exact ⟨hn, Fraction.le_equiv_left
    (Fraction.equiv_symm (Fraction.abs_of_nonnegative _ hn))
    (phase_abs_bound b T hT m j)⟩

theorem edge_vertex_bound (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (x v : Point) (m : Nat) :
    Within (realize (edgeName b T hT x v m)) (embed (x, zeroPoint))
      (Fraction.mul (duration T m) (pointNorm v)) := by
  apply nameBound_of_eventual_le _ _ _ 0
  intro j _
  exact Fraction.le_equiv_left (affine_vertex_distance x v _)
    (Fraction.mul_le_mul_nonnegative (phase_abs_bound b T hT m j)
      (pointNorm v) (pointNorm_nonnegative v))

theorem edgeName_same_start (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (x v : Point) (m : Nat)
    (hbase : timeApprox b T m = timeApprox c T m)
    (htime : AddressEquiv T hT b c) :
    NameEquiv (edgeName b T hT x v m) (edgeName c T hT x v m) := by
  intro eps heps
  let V := pointNorm v
  let delta := factorDelta V eps (pointNorm_nonnegative v)
  obtain ⟨N,hN⟩ := htime delta
    (factorDelta_positive V eps (pointNorm_nonnegative v) heps)
  refine ⟨N, ?_⟩
  intro j hj
  have ht := hN (m+j) (by omega)
  have hd := timeState_distance b c T (m+j)
  have hg := Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (Fraction.equiv_symm hd)) ht
  have hc := factor_control V eps
    (durationDifference (timeApprox c T (m+j)) (timeApprox b T (m+j))).abs
    (pointNorm_nonnegative v) (Fraction.abs_num_nonnegative _) hg
  have ha : Fraction.equiv
      (distance ((edgeName b T hT x v m).approx j)
        ((edgeName c T hT x v m).approx j))
      (Fraction.mul
        (durationDifference (timeApprox c T (m+j)) (timeApprox b T (m+j))).abs V) := by
    dsimp only [edgeName]
    rw [hbase]
    exact Fraction.equiv_trans (affine_distance x v _ _)
      (Fraction.mul_equiv (Fraction.abs_equiv (shift_difference _ _ _))
        (Fraction.equiv_refl V))
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv ha) hc

end NewtonLimitDynamics.Polygon.AffineValues
