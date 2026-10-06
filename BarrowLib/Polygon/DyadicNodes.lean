import BarrowLib.Polygon.FiniteAddress
import BarrowLib.Polygon.BinaryEndpoints
import BarrowLib.Polygon.SecantValues
import BarrowLib.Polygon.TailValues

/-! Actual dyadic nodes of the constructed binary-time domain, including
the right endpoint. A truncation lies within one cell of its time value. -/

namespace NewtonLimitDynamics.Polygon.DyadicNodes
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicBinaryPrefix HarmonicTimeComparison
open HarmonicTimeRealization CauchyValues BinaryTime SecantValues

theorem blocks_add (m j : Nat) : blocks (m+j)=blocks m*blocks j := by
  simp only [blocks,Nat.pow_add]

theorem finiteAddress_later_ticks (m k j : Nat) (hk : k<blocks m) :
    ticks (finiteAddress m k) (m+j)=k*blocks j := by
  rw [ticks_zero_tail _ m (finiteAddress_tail m k),finiteAddress_ticks m k hk]

theorem grid_time (T : Fraction) (m j : Nat) :
    Fraction.equiv (Fraction.mul (Fraction.ofInt (blocks j : Int)) (duration T (m+j)))
      (duration T m) := by
  simp only [blocks,duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_pow,
    FiniteGrowth.denominator_power_add]
  change (2:Int)^j*T.num*(T.den*2^m)=T.num*(1*(T.den*(2^m*2^j)))
  simp only [Int.one_mul]
  ac_rfl

theorem finiteAddress_time (T : Fraction) (m k j : Nat) (hk : k<blocks m) :
    Fraction.equiv (timeApprox (finiteAddress m k) T (m+j)) (countTime T m k) := by
  rw [timeApprox,finiteAddress_later_ticks m k j hk]
  have he := Fraction.mul_equiv_left (Fraction.ofInt (k : Int)) (grid_time T m j)
  apply Fraction.equiv_trans _ he
  simp only [countTime,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_mul]
  ac_nf

def nodeTime (T : Fraction) (hT : 0 ≤ T.num) (m k : Nat) : BinaryTime T hT :=
  if k=blocks m then rightTime T hT else Quotient.mk _ (finiteAddress m k)

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

theorem truncation_time_within (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num) (m : Nat) :
    TimeWithin T hT (nodeTime T hT m (ticks b m)) (Quotient.mk _ b) (duration T m) := by
  change Within (timeCoordinate T hT (nodeTime T hT m (ticks b m)))
    (BinaryTime.timeValue b T hT) (duration T m)
  rw [node_time_coordinate T hT m (ticks b m) (ticks_le_blocks b m)]
  exact TailValues.approximant_bound (BinaryTime.timeName b T hT) T hT
    (fun j => adjacent_time_bound b T j hT) m

def intervalStart (b c : Nat → Bool) (m : Nat) : Nat := min (ticks b m) (ticks c m)
def intervalCount (b c : Nat → Bool) (m : Nat) : Nat :=
  max (ticks b m) (ticks c m) - intervalStart b c m

theorem interval_end_le_blocks (b c : Nat → Bool) (m : Nat) :
    intervalStart b c m + intervalCount b c m ≤ blocks m := by
  simp only [intervalStart,intervalCount]
  have hb := ticks_le_blocks b m
  have hc := ticks_le_blocks c m
  omega

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
