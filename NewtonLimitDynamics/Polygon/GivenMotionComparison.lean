import NewtonLimitDynamics.Polygon.GeneralForcePrefix

/-! Finite comparison with supplied motion samples. A supplied trajectory's
samples are arbitrary finite data; the local cell residual and
candidate-arrival region are additional mechanical consistency premises. No
area law, polygon agreement, or limiting motion assertion is used here. -/

namespace NewtonLimitDynamics.Polygon.GivenMotionComparison
open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates ForceClasses HarmonicDyadic
open GeneralForceEndpoint GeneralForcePrefix

/-- Full-grid coordinate error allowed by finite local consistency. -/
def errorBudget (tau : Fraction) (ht : 0 < tau.num)
    (h E D : Fraction) (n : Nat) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) (TimeCalibration.inverse tau ht))
    (Fraction.mul (Fraction.ofInt (2 * (n : Int)))
      (TimeCalibration.sampleSource tau h E D))

theorem count_sample_stateDistance_le_budget (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (j : Nat) (q : Nat → Point × Point) (D : Fraction)
    (hD : 0 ≤ D.num) (hq0 : q 0 = s)
    (hcandidate : ∀ k, k < blocks j →
      o.region (cell (field o E0 hE j) (duration T j) (q k)).1)
    (hres : ∀ k, k < blocks j → Fraction.le
      (TimeCalibration.distance tau (q (k+1))
        (cell (field o E0 hE j) (duration T j) (q k))) D)
    (n : Nat) (hn : n ≤ blocks j) :
    Fraction.le (stateDistance (countState o E0 T s hE j n) (q n))
      (errorBudget tau d.calibration_positive (duration T j)
        (sampleError o E0 hE j) D (blocks j)) := by
  let S := TimeCalibration.sampleSource tau (duration T j) (sampleError o E0 hE j) D
  let C := Fraction.add (Fraction.ofInt 1)
    (TimeCalibration.inverse tau d.calibration_positive)
  have hS : 0 ≤ S.num := Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_mul _ _ (Int.le_of_lt d.calibration_positive)
        (Fraction.abs_num_nonnegative _))
      (sampleError_nonnegative o E0 hE j)) hD
  have hC : 0 ≤ C.num := Fraction.nonnegative_add _ _ (by decide)
    (Int.le_of_lt tau.den_pos)
  have hw := TimeCalibration.window_of_elapsed tau (duration T j) T L
    d.calibration_positive d.lipschitz.1 n
    (Fraction.le_equiv_left
      (Fraction.mul_equiv_left (Fraction.ofInt (n : Int))
        (Fraction.abs_of_nonnegative (duration T j) d.time_nonnegative))
      (count_time_le T d.time_nonnegative j n hn)) d.window
  have hl := TimeCalibration.run_sample_distance_le_two tau d.calibration_positive
    (field o E0 hE j) (duration T j) L (sampleError o E0 hE j) D s q
    (blocks j) d.lipschitz.1 (sampleError_nonnegative o E0 hE j) hD hq0
    (by
      intro k hk
      exact local_contract o E0 T tau L B s hE d.toConditions j _ _
        (count_region o E0 T tau L B s hE d j (k+1) (by omega))
        (hcandidate k hk)) hres n hn hw
  have hm : Fraction.le (Fraction.ofInt (2 * (n : Int)))
      (Fraction.ofInt (2 * ((blocks j : Nat) : Int))) := by
    simpa only [Fraction.le, Fraction.ofInt, Int.mul_one] using
      (show 2 * (n : Int) ≤ 2 * (blocks j : Int) by omega)
  have hb := Fraction.mul_le_mul_nonnegative hm S hS
  have hd := TimeCalibration.uncalibrated_le_distance tau d.calibration_positive
    (countState o E0 T s hE j n) (q n)
  have hs := Fraction.mul_le_mul_nonnegative_left
    (Fraction.magnitudes.le_trans hl hb) C hC
  exact Fraction.le_equiv_right (Fraction.magnitudes.le_trans hd hs) (by
    exact Fraction.equiv_refl _)

end NewtonLimitDynamics.Polygon.GivenMotionComparison
