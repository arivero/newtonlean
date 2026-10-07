import ModernLib.Foundation.Polygon.FiniteAddress
import ModernLib.Foundation.Polygon.BinaryEndpoints
import ModernLib.Foundation.Polygon.SecantValues
import ModernLib.Foundation.Polygon.TailValues
import ModernLib.Foundation.Polygon.CompletionGeometry

/-! Actual dyadic nodes of the constructed binary-time domain, including
the right endpoint. A truncation lies within one cell of its time value. -/

namespace NewtonLimitDynamics.Polygon.DyadicNodes
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix HarmonicTimeComparison
open HarmonicTimeRealization CauchyValues BinaryTime SecantValues

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem blocks_add (m j : Nat) : blocks (m+j)=blocks m*blocks j := by
  simp only [blocks,Nat.pow_add]

-- Modern dependency score: 3/5 (M=3, H=2; transitive project theorems/axioms).
theorem finiteAddress_later_ticks (m k j : Nat) (hk : k<blocks m) :
    ticks (finiteAddress m k) (m+j)=k*blocks j := by
  rw [ticks_zero_tail _ m (finiteAddress_tail m k),finiteAddress_ticks m k hk]

-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
theorem grid_time (T : Fraction) (m j : Nat) :
    Fraction.equiv (Fraction.mul (Fraction.ofInt (blocks j : Int)) (duration T (m+j)))
      (duration T m) := by
  simp only [blocks,duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_pow,
    FiniteGrowth.denominator_power_add]
  change (2:Int)^j*T.num*(T.den*2^m)=T.num*(1*(T.den*(2^m*2^j)))
  simp only [Int.one_mul]
  ac_rfl

-- Modern dependency score: 5/12 (M=5, H=7; transitive project theorems/axioms).
theorem finiteAddress_time (T : Fraction) (m k j : Nat) (hk : k<blocks m) :
    Fraction.equiv (timeApprox (finiteAddress m k) T (m+j)) (countTime T m k) := by
  rw [timeApprox,finiteAddress_later_ticks m k j hk]
  have he := Fraction.mul_equiv_left (Fraction.ofInt (k : Int)) (grid_time T m j)
  apply Fraction.equiv_trans _ he
  simp only [countTime,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_mul]
  ac_nf

def nodeTime (T : Fraction) (hT : 0 ≤ T.num) (m k : Nat) : BinaryTime T hT :=
  if k=blocks m then rightTime T hT else Quotient.mk _ (finiteAddress m k)

-- Modern dependency score: 29/91 (M=29, H=62; transitive project theorems/axioms).
theorem node_time_coordinate (T : Fraction) (hT : 0 ≤ T.num) (m k : Nat) (hk : k≤blocks m) :
    timeCoordinate T hT (nodeTime T hT m k) = embed (scalarState (countTime T m k)) := by
  by_cases he : k=blocks m
  · rw [nodeTime,if_pos he,right_time_coordinate]
    subst k
    apply Quotient.sound
    apply nameEquiv_of_levelwise_stateEquiv
    intro j
    exact ⟨⟨Fraction.equiv_symm (blocks_duration T m),Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩
  · rw [nodeTime,if_neg he]
    change realize (BinaryTime.timeName (finiteAddress m k) T hT) = _
    rw [← shiftedValue (BinaryTime.timeName (finiteAddress m k) T hT) m]
    apply Quotient.sound
    apply nameEquiv_of_levelwise_stateEquiv
    intro j
    exact ⟨⟨finiteAddress_time T m k j (by omega),Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

-- Modern dependency score: 42/108 (M=42, H=66; transitive project theorems/axioms).
theorem truncation_time_within (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num) (m : Nat) :
    TimeWithin T hT (nodeTime T hT m (ticks b m)) (Quotient.mk _ b) (duration T m) := by
  change Within (timeCoordinate T hT (nodeTime T hT m (ticks b m)))
    (BinaryTime.timeValue b T hT) (duration T m)
  rw [node_time_coordinate T hT m (ticks b m) (ticks_le_blocks b m)]
  exact TailValues.approximant_bound (BinaryTime.timeName b T hT) T hT
    (fun j => adjacent_time_bound b T j hT) m

/-- The actual times of consecutive grid nodes differ by one mesh cell. -/
-- Modern dependency score: 42/109 (M=42, H=67; transitive project theorems/axioms).
theorem adjacent_node_time_within (T : Fraction) (hT : 0 ≤ T.num)
    (m k : Nat) (hk : k<blocks m) :
    TimeWithin T hT (nodeTime T hT m k) (nodeTime T hT m (k+1)) (duration T m) := by
  unfold TimeWithin
  rw [node_time_coordinate T hT m k (by omega),
    node_time_coordinate T hT m (k+1) (by omega)]
  apply (CompletionGeometry.within_embedded_iff _ _ _).mpr
  apply Fraction.le_of_equiv
  apply Fraction.equiv_trans (scalarState_distance _ _)
  apply Fraction.equiv_trans (durationDifference_abs_symm _ _)
  apply Fraction.equiv_trans (countTime_abs_difference T m k 1 hT)
  simp only [countTime,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_one,Int.one_mul,Int.mul_one]

def intervalStart (b c : Nat → Bool) (m : Nat) : Nat := min (ticks b m) (ticks c m)
def intervalCount (b c : Nat → Bool) (m : Nat) : Nat :=
  max (ticks b m) (ticks c m) - intervalStart b c m

-- Modern dependency score: 0/4 (M=0, H=4; transitive project theorems/axioms).
theorem interval_end_le_blocks (b c : Nat → Bool) (m : Nat) :
    intervalStart b c m + intervalCount b c m ≤ blocks m := by
  simp only [intervalStart,intervalCount]
  have hb := ticks_le_blocks b m
  have hc := ticks_le_blocks c m
  omega

-- Modern dependency score: 0/10 (M=0, H=10; transitive project theorems/axioms).
theorem interval_count_time_gap (T : Fraction) (hT : 0 ≤ T.num)
    (u v m : Nat) :
    Fraction.equiv (countTime T m (max u v - min u v))
      (HarmonicTimeComparison.durationDifference (countTime T m u) (countTime T m v)).abs := by
  rcases Nat.le_total u v with huv | hvu
  · rw [Nat.max_eq_right huv,Nat.min_eq_left huv]
    have hs : u + (v-u) = v := Nat.add_sub_of_le huv
    simpa only [countTime,hs] using
      (Fraction.equiv_symm (countTime_abs_difference T m u (v-u) hT))
  · rw [Nat.max_eq_left hvu,Nat.min_eq_right hvu]
    have hs : v + (u-v) = u := Nat.add_sub_of_le hvu
    simpa only [countTime,hs] using Fraction.equiv_trans (Fraction.equiv_symm
      (countTime_abs_difference T m v (u-v) hT))
      (durationDifference_abs_symm _ _)

end NewtonLimitDynamics.Polygon.DyadicNodes
