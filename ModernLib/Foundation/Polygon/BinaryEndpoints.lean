import ModernLib.Foundation.Polygon.BinaryTime
import BarrowLib.Polygon.GeometricTail

/-! Constructed time coordinates and endpoints, with retained public names.
No motion or harmonic coefficient is a premise. -/
namespace NewtonLimitDynamics.Polygon.HarmonicTimeRealization
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicStability HarmonicDyadic HarmonicBinaryPrefix
open HarmonicTimeComparison HarmonicComparison HarmonicAccumulation CauchyValues BinaryTime

def timeCoordinate (T : Fraction) (hT : 0 ≤ T.num) :
    BinaryTime T hT → Value :=
  Quotient.lift (fun b => BinaryTime.timeValue b T hT)
    (fun _ _ h => Quotient.sound h)

theorem timeCoordinate_injective (T : Fraction) (hT : 0 ≤ T.num) :
    ∀ x y : BinaryTime T hT,
      timeCoordinate T hT x = timeCoordinate T hT y → x = y := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ b =>
    induction y using Quotient.inductionOn with
    | _ c =>
      change BinaryTime.timeValue b T hT =
        BinaryTime.timeValue c T hT at hxy
      have hnames : NameEquiv (BinaryTime.timeName b T hT)
          (BinaryTime.timeName c T hT) := Quotient.exact hxy
      exact Quotient.sound hnames

def TimeWithin (T : Fraction) (hT : 0 ≤ T.num)
    (x y : BinaryTime T hT) (R : Fraction) : Prop :=
  Within (timeCoordinate T hT x) (timeCoordinate T hT y) R

theorem timeWithin_address (b c : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) (R : Fraction) :
    TimeWithin T hT (Quotient.mk _ b) (Quotient.mk _ c) R ↔
      NameBound (BinaryTime.timeName b T hT)
        (BinaryTime.timeName c T hT) R := Iff.rfl

def leftAddress : Nat → Bool := fun _ => false
def rightAddress : Nat → Bool := fun _ => true

def leftTime (T : Fraction) (hT : 0 ≤ T.num) : BinaryTime T hT :=
  Quotient.mk _ leftAddress
def rightTime (T : Fraction) (hT : 0 ≤ T.num) : BinaryTime T hT :=
  Quotient.mk _ rightAddress

theorem left_time_state_equiv (T : Fraction) (j : Nat) :
    stateEquiv (timeState leftAddress T j)
      (scalarState (Fraction.ofInt 0)) := by
  have ht : Fraction.equiv (timeApprox leftAddress T j)
      (Fraction.ofInt 0) := by
    have hz : ticks leftAddress j = 0 :=
      all_zero_ticks j
    simp only [timeApprox, hz, Fraction.equiv, Fraction.mul,
      Fraction.ofInt]
    simp
  exact ⟨⟨ht, Fraction.equiv_refl _⟩,
    ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩

theorem left_time_coordinate (T : Fraction) (hT : 0 ≤ T.num) :
    timeCoordinate T hT (leftTime T hT) =
      embed (scalarState (Fraction.ofInt 0)) := by
  apply Quotient.sound
  intro eps heps
  refine ⟨0, ?_⟩
  intro j _
  have he := (distance_zero_iff_stateEquiv
    (timeState leftAddress T j)
    (scalarState (Fraction.ofInt 0))).mpr
      (left_time_state_equiv T j)
  have hself := stateSub_self_norm_zero
    (scalarState (Fraction.ofInt 0))
  have hle : Fraction.le
      (distance (timeState leftAddress T j)
        (scalarState (Fraction.ofInt 0)))
      (distance (scalarState (Fraction.ofInt 0))
        (scalarState (Fraction.ofInt 0))) := Fraction.le_of_equiv
    (Fraction.equiv_trans he (Fraction.equiv_symm hself))
  exact Fraction.magnitudes.lt_of_le_lt hle
    (distance_self_lt _ eps heps)

theorem right_ticks (j : Nat) : ticks rightAddress j + 1 = blocks j := by
  induction j with
  | zero => simp [ticks, rightAddress, bit, blocks]
  | succ j ih =>
      rw [ticks, blocks_succ]
      simp only [rightAddress, bit, ite_true]
      omega

theorem right_time_difference (T : Fraction) (j : Nat) :
    Fraction.equiv (durationDifference (timeApprox rightAddress T j) T)
      (duration T j) := by
  have hk : (ticks rightAddress j : Int) + 1 = (2 : Int) ^ j := by
    have hr := right_ticks j
    have hr' := congrArg Int.ofNat hr
    change ((ticks rightAddress j + 1 : Nat) : Int) =
      ((2 ^ j : Nat) : Int) at hr'
    rw [Int.natCast_add, Int.natCast_one, Int.natCast_pow] at hr'
    exact hr'
  simp only [timeApprox, durationDifference, negF, Fraction.equiv,
    Fraction.add, Fraction.mul, Fraction.ofInt, duration]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  rw [← hk]
  simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
  ac_nf <;> omega

theorem right_time_distance (T : Fraction) (j : Nat)
    (hT : 0 ≤ T.num) :
    Fraction.equiv (distance (timeState rightAddress T j)
      (scalarState T)) (duration T j) := by
  have h₁ := scalarState_distance (timeApprox rightAddress T j) T
  have h₂ := durationDifference_abs_symm T (timeApprox rightAddress T j)
  have h₃ := Fraction.abs_equiv (right_time_difference T j)
  have h₄ := Fraction.abs_of_nonnegative (duration T j) hT
  exact Fraction.equiv_trans h₁
    (Fraction.equiv_trans h₂ (Fraction.equiv_trans h₃ h₄))

theorem right_time_coordinate (T : Fraction) (hT : 0 ≤ T.num) :
    timeCoordinate T hT (rightTime T hT) = embed (scalarState T) := by
  apply Quotient.sound
  intro eps heps
  obtain ⟨N, hN⟩ := duration_eventually_small T eps hT heps
  refine ⟨N, ?_⟩
  intro j hj
  exact Fraction.magnitudes.lt_of_le_lt
    ((Fraction.equiv_iff_mutual_le _ _).mp
      (right_time_distance T j hT)).1 (hN j hj)

end NewtonLimitDynamics.Polygon.HarmonicTimeRealization
