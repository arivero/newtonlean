import BarrowLib.Polygon.IntegerRefinement
import NewtonLimitDynamics.Polygon.HarmonicTimeRealization

/-! Agreement of endpoint and global-prefix harmonic names at dyadic times. -/

namespace NewtonLimitDynamics.Polygon.HarmonicConstructionAgreement

open NewtonLimitDynamics
open TimeSubdivision
open HarmonicStability
open HarmonicDyadic
open HarmonicBinaryPrefix
open HarmonicTimeComparison
open HarmonicTimeRealization
open CauchyValues
open BinaryTime
open PointBounds

private theorem factor_nonnegative (w : Fraction) :
    0 ≤ (Fraction.add (Fraction.ofInt 1) w.abs).num :=
  Fraction.nonnegative_add _ _ (by decide) (Fraction.abs_num_nonnegative w)

/-- A nonnegative dyadic subduration of a short window is short. -/
theorem subduration_small (w T : Fraction) (m : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    DyadicSmallTime w (duration T m) := by
  have h := Fraction.mul_le_mul_nonnegative
    (duration_le_time T m hT) (Fraction.add (Fraction.ofInt 1) w.abs)
    (factor_nonnegative w)
  exact Fraction.magnitudes.le_trans h hs

theorem unit_tail_level (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m j : Nat)
    (htick : ticks b m = 1) (hz : ∀ i, m ≤ i → b i = false) :
    stateEquiv (endpoint w (duration T m) s j)
      (prefixState b w T s (m + j)) := by
  have hcount : ticks b (m + j) = blocks j := by
    rw [ticks_zero_tail b m hz j, htick]
    simp
  have hd := duration_nested T m j
  simpa only [endpoint, prefixState, hcount] using
    schedule_replicate_congr w (duration (duration T m) j)
      (duration T (m + j)) hd (blocks j) s s
      ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
        ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩

/-- For a one-tick address, the endpoint and prefix Cauchy names agree. -/
theorem unit_tail_names (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (htick : ticks b m = 1) (hz : ∀ i, m ≤ i → b i = false) :
    NameEquiv
      (endpointName w (duration T m) s hT (subduration_small w T m hT hs))
      (prefixName b w T s hT hs) := by
  intro eps heps
  obtain ⟨N, hN⟩ := (prefixName b w T s hT hs).cauchy eps heps
  refine ⟨N, ?_⟩
  intro j hj
  have hshift : N ≤ m + j := by omega
  have he := unit_tail_level b w T s m j htick hz
  have he' : Fraction.equiv
      (distance (endpoint w (duration T m) s j) (prefixState b w T s j))
      (distance (prefixState b w T s (m+j)) (prefixState b w T s j)) :=
    stateNorm_equiv (stateSub_congr he
    ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩)
  exact Fraction.magnitudes.lt_of_le_lt
    ((Fraction.equiv_iff_mutual_le _ _).mp he').1
    (hN (m + j) j hshift hj)

/-- Equality of the two completed state values at reciprocal dyadic times. -/
theorem unit_tail_value (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (m : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (htick : ticks b m = 1) (hz : ∀ i, m ≤ i → b i = false) :
    timeValue w s ⟨duration T m, hT, subduration_small w T m hT hs⟩ =
      gammaValue w T s hT hs (Quotient.mk _ b) := by
  exact Quotient.sound (unit_tail_names b w T s m hT hs htick hz)

theorem full_window_value (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    timeValue w s ⟨T,hT,hs⟩ = gammaValue w T s hT hs (rightTime T hT) :=
  (right_endpoint_value w T s hT hs).symm

theorem zero_window_value (b : Nat → Bool) (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (hz : T.num = 0) :
    timeValue w s ⟨T,hT,hs⟩ = gammaValue w T s hT hs (Quotient.mk _ b) := by
  have he : timeValue w s ⟨T,hT,hs⟩ = embed s :=
    Quotient.sound (nameEquiv_of_levelwise_stateEquiv
      (endpointName w T s hT hs) (constantName s)
      (fun j => zero_time_endpoint w T s j hz))
  exact he.trans (zero_time_value b w T s hT hs hz).symm

private def one : Fraction := Fraction.ofInt 1
private def quarter : Fraction := ⟨1,4,by decide⟩
private def threeSixteenths : Fraction := ⟨3,16,by decide⟩
private def testState : Point × Point :=
  ((one,Fraction.ofInt 0),(Fraction.ofInt 0,one))
private def threeQuarterAddress (j : Nat) : Bool := j < 2

/-- A finite endpoint schedule at 3T/4 differs from the same-time global
three-cell prefix. Limit agreement cannot be proved by equating these cells. -/
theorem three_tick_finite_control :
    Fraction.equiv
      (distance (endpoint one threeSixteenths testState 0)
        (prefixState threeQuarterAddress one quarter testState 2))
      ⟨426975,16777216,by decide⟩ := by decide

theorem three_tick_finite_identity_false :
    ¬ stateEquiv (endpoint one threeSixteenths testState 0)
      (prefixState threeQuarterAddress one quarter testState 2) := by decide

end NewtonLimitDynamics.Polygon.HarmonicConstructionAgreement
