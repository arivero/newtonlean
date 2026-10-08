import BarrowLib.Polygon.TimeCalibration
import BarrowLib.Polygon.CentralSchedule
import BarrowLib.Polygon.RadialSector
import BarrowLib.Polygon.TriangleExchange
import BarrowLib.Polygon.GeometricTail
import BarrowLib.Polygon.PolygonFanArea
import BarrowLib.Common.Exhaustion

/-! Finite comparison of independent motion samples with drift/kick polygons.
TimeCalibration already proves the finite comparison recurrence, and
PolygonFanArea already sums triangle errors. This file derives the missing
quadratic-remainder budgets and their exhaustion; it constructs no completed
trajectory and assumes no polygon agreement, area law or vanishing area.

Source of these coordinate statements and derivations: the original English
statements and Lean proofs below, using the named finite library results.
This records project formalization authorship, not discovery or priority.
The force-comparison inequality and local quadratic motion remainder are
separate explicit regularity/mechanical premises of this reconstruction;
Newton's text states neither as an axiom.
No post-Principia theorem or completion is used in the proofs.
-/
namespace NewtonLimitDynamics.Polygon.MotionSampling
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates
open HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization PolygonFanArea

private def one : Fraction := Fraction.ofInt 1
private def zero : Fraction := Fraction.ofInt 0

def remainder (C T : Fraction) (j : Nat) : Fraction :=
  Fraction.mul C (Fraction.mul (duration T j) (duration T j))

def stateBudget (C T : Fraction) (j : Nat) : Fraction :=
  Fraction.mul (Fraction.mul (Fraction.ofInt 2) (Fraction.mul C T)) (duration T j)

theorem remainder_nonnegative (C T : Fraction) (j : Nat) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) :
    0 ≤ (remainder C T j).num :=
  Fraction.nonnegative_mul _ _ hC (Fraction.nonnegative_mul _ _ hT hT)

theorem stateBudget_nonnegative (C T : Fraction) (j : Nat) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) :
    0 ≤ (stateBudget C T j).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hC hT)) hT

theorem count_remainder (C T : Fraction) (j : Nat) :
    Fraction.equiv (Fraction.mul (Fraction.ofInt (blocks j : Int)) (remainder C T j))
      (Fraction.mul (Fraction.mul C T) (duration T j)) := by
  have he := Fraction.mul_equiv_left C (blocks_duration T j)
  have he' := Fraction.mul_equiv_right (duration T j) he
  apply Fraction.equiv_trans (b := Fraction.mul (Fraction.mul C
    (Fraction.mul (Fraction.ofInt (blocks j : Int)) (duration T j))) (duration T j)) ?_ he'
  simp only [remainder,Fraction.equiv,Fraction.mul]
  ac_nf

/-- A finite force comparison and independent one-step motion residual give
an actual state error bound. The candidate may depart from the polygon
recurrence; only force values at the two used arrivals are compared. -/
theorem finite_sample_bound (a : Point → Point) (h L D : Fraction)
    (s : Point × Point) (q : Nat → Point × Point) (N : Nat)
    (hL : 0 ≤ L.num) (hD : 0 ≤ D.num) (hq0 : q 0 = s)
    (hforce : ∀ p r, Fraction.le (pointDistance (a p) (a r))
      (Fraction.mul L (pointDistance p r)))
    (hres : ∀ k, k < N → Fraction.le (stateDistance (q (k+1)) (cell a h (q k))) D)
    (hw : TimeCalibration.Window one h L (by decide) N)
    (n : Nat) (hn : n ≤ N) :
    Fraction.le (stateDistance (BoundedIteration.run a h s n) (q n))
      (Fraction.mul (Fraction.ofInt (2 * (N : Int))) D) := by
  have hstep := TimeCalibration.run_sample_distance_le_two one (by decide) a h L zero D s q N
    hL (by decide) hD hq0
    (fun k _ => Fraction.le_equiv_right (hforce _ _) (Fraction.equiv_symm (Fraction.add_zero _)))
    (fun k hk => Fraction.le_equiv_left
      (TimeCalibration.distance_unit_calibration _ _) (hres k hk)) n hn
    (TimeCalibration.window_mono one h L (by decide) hL n N hn hw)
  have hs : Fraction.equiv (TimeCalibration.sampleSource one h zero D) D :=
    Fraction.equiv_trans (Fraction.add_equiv_right D (Fraction.mul_zero _))
      (Fraction.equiv_trans (Fraction.add_comm _ _) (Fraction.add_zero D))
  have hcount : Fraction.le (Fraction.ofInt (2 * (n : Int))) (Fraction.ofInt (2 * (N : Int))) := by
    simp only [Fraction.le,Fraction.ofInt,Int.mul_one]
    omega
  exact Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right (Fraction.le_equiv_left
      (Fraction.equiv_symm (TimeCalibration.distance_unit_calibration _ _)) hstep)
      (Fraction.mul_equiv_left _ hs)) (Fraction.mul_le_mul_nonnegative hcount D hD)

/-- Dyadic cell widths derive the full-grid error `2*C*T*h` from a local
`C*h²` residual; shrinking error and sample agreement follow from it below. -/
theorem dyadic_sample_bound (a : Point → Point) (C T L : Fraction)
    (s : Point × Point) (q : Nat → Nat → Point × Point)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hL : 0 ≤ L.num)
    (hq0 : ∀ j, q j 0 = s)
    (hforce : ∀ p r, Fraction.le (pointDistance (a p) (a r))
      (Fraction.mul L (pointDistance p r)))
    (hres : ∀ j k, k < blocks j → Fraction.le
      (stateDistance (q j (k+1)) (cell a (duration T j) (q j k))) (remainder C T j))
    (hw : Fraction.le (Fraction.mul T (TimeCalibration.rate one L (by decide))) ⟨1,2,by decide⟩)
    (j n : Nat) (hn : n ≤ blocks j) :
    Fraction.le (stateDistance (BoundedIteration.run a (duration T j) s n) (q j n)) (stateBudget C T j) := by
  have hwin := TimeCalibration.window_of_elapsed one (duration T j) T L (by decide) hL (blocks j)
    (Fraction.le_of_equiv (Fraction.equiv_trans
      (Fraction.mul_equiv_left _ (Fraction.abs_of_nonnegative _ hT)) (blocks_duration T j))) hw
  have hb := finite_sample_bound a (duration T j) L (remainder C T j) s (q j) (blocks j)
    hL (remainder_nonnegative C T j hC hT) (hq0 j) hforce (hres j) hwin n hn
  apply Fraction.le_equiv_right hb
  apply Fraction.equiv_trans (b := Fraction.mul (Fraction.ofInt 2)
    (Fraction.mul (Fraction.ofInt (blocks j : Int)) (remainder C T j)))
  · simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt]
    ac_nf
  · exact Fraction.equiv_trans (Fraction.mul_equiv_left _ (count_remainder C T j))
      (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))

/-- A nonnegative constant multiple of a shrinking dyadic width vanishes. -/
theorem dyadic_scaled_vanishes (K T : Fraction) (hK : 0 ≤ K.num) (hT : 0 ≤ T.num) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun j => Fraction.mul K (duration T j)) := by
  intro eps heps
  obtain ⟨N,hN⟩ := duration_eventually_small T (factorDelta K eps hK) hT
    (factorDelta_positive K eps hK heps)
  refine ⟨N,fun j hj => ?_⟩
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv (Fraction.mul_comm _ _))
    (factor_control K eps (duration T j) hK hT (hN j hj))

theorem state_budgets_vanish (C T : Fraction) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) :
    Exhaustion.VanishingDifference Fraction.magnitudes (stateBudget C T) :=
  dyadic_scaled_vanishes _ T
    (Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hC hT)) hT

theorem dyadic_sample_agreement (a : Point → Point) (C T L : Fraction)
    (s : Point × Point) (q : Nat → Nat → Point × Point)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hL : 0 ≤ L.num)
    (hq0 : ∀ j, q j 0 = s)
    (hforce : ∀ p r, Fraction.le (pointDistance (a p) (a r))
      (Fraction.mul L (pointDistance p r)))
    (hres : ∀ j k, k < blocks j → Fraction.le
      (stateDistance (q j (k+1)) (cell a (duration T j) (q j k))) (remainder C T j))
    (hw : Fraction.le (Fraction.mul T (TimeCalibration.rate one L (by decide))) ⟨1,2,by decide⟩) :
    ∀ eps, 0 < eps.num → ∃ N, ∀ j, N ≤ j → ∀ n, n ≤ blocks j →
      Fraction.lt (stateDistance (BoundedIteration.run a (duration T j) s n) (q j n)) eps := by
  intro eps heps
  obtain ⟨N,hN⟩ := state_budgets_vanish C T hC hT eps heps
  exact ⟨N,fun j hj n hn => Fraction.magnitudes.lt_of_le_lt
    (dyadic_sample_bound a C T L s q hC hT hL hq0 hforce hres hw j n hn) (hN j hj)⟩

theorem position_distance_le_state (s t : Point × Point) :
    Fraction.le (pointDistance s.1 t.1) (stateDistance s t) :=
  Fraction.le_add_nonnegative _ _ (pointNorm_nonnegative _)

theorem velocity_distance_le_state (s t : Point × Point) :
    Fraction.le (pointDistance s.2 t.2) (stateDistance s t) :=
  Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ (pointNorm_nonnegative _))
    (Fraction.add_comm _ _)

/-- The bilinear difference uses one position bound and the other velocity
bound. No conservation or small-area premise enters this inequality. -/
theorem momentum_difference_bound (s t : Point × Point) (R V E : Fraction)
    (hR : 0 ≤ R.num) (hV : 0 ≤ V.num)
    (hp : Fraction.le (pointNorm s.1) R) (hv : Fraction.le (pointNorm t.2) V)
    (he : Fraction.le (stateDistance s t) E) :
    Fraction.le (durationDifference (TimeSubdivision.det s.1 s.2) (TimeSubdivision.det t.1 t.2)).abs
      (Fraction.mul (Fraction.add R V) E) := by
  have hid : Fraction.equiv
      (durationDifference (TimeSubdivision.det s.1 s.2) (TimeSubdivision.det t.1 t.2))
      (Fraction.add (TimeSubdivision.det (pointSub t.1 s.1) t.2)
        (TimeSubdivision.det s.1 (pointSub t.2 s.2))) := by
    simp only [durationDifference,HarmonicStability.negF,TimeSubdivision.det,pointSub,
      pointAdd,pointNeg,Fraction.equiv,Fraction.add,Fraction.mul,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf <;> omega
  have hpos := Fraction.magnitudes.le_trans (position_distance_le_state s t) he
  have hvel := Fraction.magnitudes.le_trans (velocity_distance_le_state s t) he
  have hb1 := Fraction.magnitudes.le_trans (TriangleBounds.det_abs_le_product _ _)
    (Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative_left hv (pointNorm (pointSub t.1 s.1)) (pointNorm_nonnegative _))
      (Fraction.mul_le_mul_nonnegative
        (Fraction.le_equiv_left (pointDistance_symm t.1 s.1) hpos) V hV))
  have hb2 := Fraction.magnitudes.le_trans (TriangleBounds.det_abs_le_product _ _)
    (Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative hp (pointNorm (pointSub t.2 s.2)) (pointNorm_nonnegative _))
      (Fraction.mul_le_mul_nonnegative_left
        (Fraction.le_equiv_left (pointDistance_symm t.2 s.2) hvel) R hR))
  have hab := Fraction.magnitudes.le_trans (Fraction.abs_add_le _ _) (Fraction.add_le_add hb1 hb2)
  exact Fraction.le_equiv_right (Fraction.le_equiv_left (Fraction.abs_equiv hid) hab)
    (Fraction.equiv_trans (Fraction.add_equiv (Fraction.mul_comm E V) (Fraction.equiv_refl _))
      (Fraction.equiv_trans (Fraction.add_comm _ _) (Fraction.equiv_symm (Fraction.add_mul _ _ _))))

theorem difference_triangle (a b c : Fraction) :
    Fraction.le (durationDifference a c).abs
      (Fraction.add (durationDifference a b).abs (durationDifference b c).abs) :=
  Fraction.le_equiv_left (Fraction.abs_equiv (durationDifference_chain a b c))
    (Fraction.abs_add_le _ _)

def cellAreaBudget (h R P V E D : Fraction) : Fraction :=
  Fraction.add (Fraction.mul h.abs (Fraction.mul (Fraction.add R V) E)) (Fraction.mul P D)

/-- A true motion chord is compared with one mechanical drift triangle.
The state discrepancy and local motion residual are separate errors. -/
theorem cell_area_error (a : Point → Point) (h R P V E D : Fraction)
    (s t u : Point × Point) (hR : 0 ≤ R.num) (hV : 0 ≤ V.num)
    (hp : Fraction.le (pointNorm s.1) R) (htp : Fraction.le (pointNorm t.1) P)
    (htv : Fraction.le (pointNorm t.2) V)
    (he : Fraction.le (stateDistance s t) E)
    (hr : Fraction.le (stateDistance u (cell a h t)) D) :
    Fraction.le (durationDifference (TimeSubdivision.det s.1 (cell a h s).1)
      (TimeSubdivision.det t.1 u.1)).abs (cellAreaBudget h R P V E D) := by
  have hm := momentum_difference_bound s t R V E hR hV hp htv he
  have hm' : Fraction.le
      (durationDifference (TimeSubdivision.det s.1 (cell a h s).1)
        (Fraction.mul h (TimeSubdivision.det t.1 t.2))).abs
      (Fraction.mul h.abs (Fraction.mul (Fraction.add R V) E)) := by
    have hid : Fraction.equiv
        (durationDifference (TimeSubdivision.det s.1 (cell a h s).1)
          (Fraction.mul h (TimeSubdivision.det t.1 t.2)))
        (Fraction.mul h (durationDifference (TimeSubdivision.det s.1 s.2) (TimeSubdivision.det t.1 t.2))) := by
      apply Fraction.equiv_trans (Fraction.add_equiv_left _
        (HarmonicDyadic.neg_equiv (CentralSchedule.det_cell_area s.1 s.2 h)))
      simp only [durationDifference,HarmonicStability.negF,Fraction.equiv,Fraction.add,Fraction.mul,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
      ac_nf <;> omega
    exact Fraction.le_equiv_left (Fraction.equiv_trans (Fraction.abs_equiv hid) (Fraction.abs_mul _ _))
      (Fraction.mul_le_mul_nonnegative_left hm h.abs (Fraction.abs_num_nonnegative h))
  have hr' := det_inertial_remainder_bound t.1 t.2 u.1 h P D htp
    (Fraction.magnitudes.le_trans (position_distance_le_state u (cell a h t)) hr)
  exact Fraction.magnitudes.le_trans
    (difference_triangle (TimeSubdivision.det s.1 (cell a h s).1)
      (Fraction.mul h (TimeSubdivision.det t.1 t.2)) (TimeSubdivision.det t.1 u.1))
    (Fraction.add_le_add hm' hr')

/-- Finite chord fans inherit a derived error bound. It compares numeric
triangle sums; unions and curved areas are treated by the explicit area rules. -/
theorem fan_comparison_bound (a : Point → Point) (h R P V E D : Fraction)
    (s : Point × Point) (q : Nat → Point × Point) (n : Nat)
    (hR : 0 ≤ R.num) (hV : 0 ≤ V.num)
    (hp : ∀ k, k < n → Fraction.le (pointNorm (BoundedIteration.run a h s k).1) R)
    (hqp : ∀ k, k < n → Fraction.le (pointNorm (q k).1) P)
    (hqv : ∀ k, k < n → Fraction.le (pointNorm (q k).2) V)
    (he : ∀ k, k < n → Fraction.le (stateDistance (BoundedIteration.run a h s k) (q k)) E)
    (hr : ∀ k, k < n → Fraction.le (stateDistance (q (k+1)) (cell a h (q k))) D) :
    Fraction.le (durationDifference (fan (fun k => (BoundedIteration.run a h s k).1) n)
      (fan (fun k => (q k).1) n)).abs
      (Fraction.mul (Fraction.ofInt n) (cellAreaBudget h R P V E D)) :=
  fan_error (fun k => (q k).1) (fun k => (BoundedIteration.run a h s k).1) _ n
    (fun k hk => cell_area_error a h R P V E D _ _ _ hR hV (hp k hk) (hqp k hk)
      (hqv k hk) (he k hk) (hr k hk))

def fanCoefficient (C T R P V : Fraction) : Fraction :=
  Fraction.mul T (Fraction.mul C (Fraction.add P
    (Fraction.mul (Fraction.mul (Fraction.ofInt 2) T) (Fraction.add R V))))

def fanBudget (C T R P V : Fraction) (j : Nat) : Fraction :=
  Fraction.mul (fanCoefficient C T R P V) (duration T j)

theorem fanCoefficient_nonnegative (C T R P V : Fraction)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hR : 0 ≤ R.num)
    (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) : 0 ≤ (fanCoefficient C T R P V).num :=
  Fraction.nonnegative_mul _ _ hT (Fraction.nonnegative_mul _ _ hC
    (Fraction.nonnegative_add _ _ hP (Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_mul _ _ (by decide) hT) (Fraction.nonnegative_add _ _ hR hV))))

theorem count_cellAreaBudget (C T R P V : Fraction) (j : Nat) (hT : 0 ≤ T.num) :
    Fraction.equiv (Fraction.mul (Fraction.ofInt (blocks j : Int))
      (cellAreaBudget (duration T j) R P V (stateBudget C T j) (remainder C T j)))
      (fanBudget C T R P V j) := by
  let K := Fraction.mul C (Fraction.add P
    (Fraction.mul (Fraction.mul (Fraction.ofInt 2) T) (Fraction.add R V)))
  have hc : Fraction.equiv
      (cellAreaBudget (duration T j) R P V (stateBudget C T j) (remainder C T j))
      (remainder K T j) := by
    unfold cellAreaBudget
    apply Fraction.equiv_trans (Fraction.add_equiv
      (Fraction.mul_equiv_right _ (Fraction.abs_of_nonnegative (duration T j) hT)) (Fraction.equiv_refl _))
    simp only [K,remainder,stateBudget,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
    ac_nf
  exact Fraction.equiv_trans (Fraction.mul_equiv_left _ hc)
    (Fraction.equiv_trans (count_remainder K T j)
      (Fraction.mul_equiv_right _ (Fraction.mul_comm K T)))

/-- All force-polygon/sample fan discrepancies tend to zero from local
quadratic mechanical consistency and finite bounds. No area-law premise is
used. `R` bounds the constructed polygon, while `P,V` bound the given samples. -/
theorem dyadic_fan_comparison (a : Point → Point) (C T L R P V : Fraction)
    (s : Point × Point) (q : Nat → Nat → Point × Point)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hL : 0 ≤ L.num)
    (hR : 0 ≤ R.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num)
    (hq0 : ∀ j, q j 0 = s)
    (hforce : ∀ p r, Fraction.le (pointDistance (a p) (a r))
      (Fraction.mul L (pointDistance p r)))
    (hres : ∀ j k, k < blocks j → Fraction.le
      (stateDistance (q j (k+1)) (cell a (duration T j) (q j k))) (remainder C T j))
    (hw : Fraction.le (Fraction.mul T (TimeCalibration.rate one L (by decide))) ⟨1,2,by decide⟩)
    (hp : ∀ j k, k < blocks j → Fraction.le
      (pointNorm (BoundedIteration.run a (duration T j) s k).1) R)
    (hqp : ∀ j k, k < blocks j → Fraction.le (pointNorm (q j k).1) P)
    (hqv : ∀ j k, k < blocks j → Fraction.le (pointNorm (q j k).2) V) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun j =>
      (durationDifference (fan (fun k => (BoundedIteration.run a (duration T j) s k).1) (blocks j))
        (fan (fun k => (q j k).1) (blocks j))).abs) := by
  have hb (j : Nat) := fan_comparison_bound a (duration T j) R P V (stateBudget C T j)
    (remainder C T j) s (q j) (blocks j) hR hV (hp j) (hqp j) (hqv j)
    (fun k hk => dyadic_sample_bound a C T L s q hC hT hL hq0 hforce hres hw j k (by omega)) (hres j)
  have hv := dyadic_scaled_vanishes (fanCoefficient C T R P V) T
    (fanCoefficient_nonnegative C T R P V hC hT hR hP hV) hT
  intro eps heps
  obtain ⟨N,hN⟩ := hv eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_equiv_right (hb j) (count_cellAreaBudget C T R P V j hT)) (hN j hj)⟩

theorem duration_le_total (T : Fraction) (j : Nat) (hT : 0 ≤ T.num) :
    Fraction.le (duration T j) T := by
  have hp : 1 ≤ (2 : Int)^j := by have h : 0 < (2 : Int)^j := Int.pow_pos (by decide); omega
  have hm := Int.mul_le_mul_of_nonneg_left hp (Int.mul_nonneg hT (Int.le_of_lt T.den_pos))
  simpa only [Fraction.le,duration,Int.mul_one,Int.mul_assoc] using hm

theorem remainder_le_width (C T : Fraction) (j : Nat) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) :
    Fraction.le (remainder C T j) (Fraction.mul (Fraction.mul C T) (duration T j)) :=
  Fraction.le_equiv_right
    (Fraction.mul_le_mul_nonnegative_left
      (Fraction.mul_le_mul_nonnegative (duration_le_total T j hT) (duration T j) hT) C hC)
    (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))

/-- The actual candidate displacement is bounded by its velocity drift plus
its local mechanical residual. No polygon/curve agreement is used here. -/
theorem position_step_bound (a : Point → Point) (h V D : Fraction)
    (s t : Point × Point) (hv : Fraction.le (pointNorm s.2) V)
    (hr : Fraction.le (stateDistance t (cell a h s)) D) :
    Fraction.le (pointDistance t.1 s.1) (Fraction.add D (Fraction.mul h.abs V)) := by
  have hd : Fraction.equiv (pointDistance (cell a h s).1 s.1)
      (Fraction.mul h.abs (pointNorm s.2)) :=
    Fraction.equiv_trans (pointNorm_equiv (ConvexCover.drift_offset h s.1 s.2)) (pointNorm_scale h s.2)
  exact Fraction.magnitudes.le_trans (pointDistance_triangle t.1 (cell a h s).1 s.1)
    (Fraction.add_le_add (Fraction.magnitudes.le_trans (position_distance_le_state t (cell a h s)) hr)
      (Fraction.le_equiv_left hd (Fraction.mul_le_mul_nonnegative_left hv h.abs (Fraction.abs_num_nonnegative h))))

theorem det_chord_bound (p q : Point) (P D : Fraction) (hP : 0 ≤ P.num)
    (hp : Fraction.le (pointNorm p) P) (hd : Fraction.le (pointDistance q p) D) :
    Fraction.le (TimeSubdivision.det p q).abs (Fraction.mul P D) := by
  have he : Fraction.equiv (TimeSubdivision.det p q) (TimeSubdivision.det p (pointSub q p)) := by
    simp only [TimeSubdivision.det,pointSub,pointAdd,pointNeg,Fraction.equiv,Fraction.add,Fraction.mul,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf <;> omega
  exact Fraction.le_equiv_left (Fraction.abs_equiv he)
    (Fraction.magnitudes.le_trans (TriangleBounds.det_abs_le_product _ _)
      (Fraction.magnitudes.le_trans
        (Fraction.mul_le_mul_nonnegative hp (pointNorm (pointSub q p)) (pointNorm_nonnegative _))
        (Fraction.mul_le_mul_nonnegative_left hd P hP)))

def slopeCoefficient (r P V C T : Fraction) (hr : 0 < r.num) : Fraction :=
  Fraction.mul (TimeCalibration.inverse (Fraction.mul r r) (Int.mul_pos hr hr))
    (Fraction.mul P (Fraction.add V (Fraction.mul C T)))

theorem slopeCoefficient_nonnegative (r P V C T : Fraction) (hr : 0 < r.num)
    (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) :
    0 ≤ (slopeCoefficient r P V C T hr).num :=
  Fraction.nonnegative_mul _ _ (Int.le_of_lt (Fraction.mul r r).den_pos)
    (Fraction.nonnegative_mul _ _ hP (Fraction.nonnegative_add _ _ hV (Fraction.nonnegative_mul _ _ hC hT)))

/-- The slope width of an actual curve cell follows from its radial lower
bound and mechanical displacement. In this chart `g(t)` is the x-coordinate
of the ray point at slope `t`. The lower bound is derived from monotonicity. -/
theorem radial_width_bound (a : Point → Point) (C T P V : Fraction)
    (g : Fraction → Fraction) {l r : Fraction} (p : MonotoneRectangles.Partition l r)
    (q : Nat → Point × Point) (j k : Nat) (hk : k < p.count)
    (hg : MonotoneRectangles.MonotoneOn g l r) (hbase : 0 < (g l).num)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hP : 0 ≤ P.num)
    (hp : Fraction.le (pointNorm (q k).1) P) (hv : Fraction.le (pointNorm (q k).2) V)
    (hchart : ∀ i, i ≤ p.count → pointEquiv (q i).1 (RadialSector.ray (g (p.nodes i)) (p.nodes i)))
    (hres : Fraction.le (stateDistance (q (k+1)) (cell a (duration T j) (q k))) (remainder C T j)) :
    Fraction.le (MonotoneRectangles.width p k)
      (Fraction.mul (slopeCoefficient (g l) P V C T hbase) (duration T j)) := by
  let R := g l
  let W := MonotoneRectangles.width p k
  let M := Fraction.mul R R
  have hM : 0 < M.num := Int.mul_pos hbase hbase
  have hW : 0 ≤ W.num := (difference_nonnegative_iff _ _).mpr (p.ordered k hk)
  have hleft := hg l (p.nodes k) (Fraction.magnitudes.le_refl _)
    (MonotoneRectangles.node_bounds p k (by omega)).1 (MonotoneRectangles.node_bounds p k (by omega)).2
  have hright := hg l (p.nodes (k+1)) (Fraction.magnitudes.le_refl _)
    (MonotoneRectangles.node_bounds p (k+1) (by omega)).1 (MonotoneRectangles.node_bounds p (k+1) (by omega)).2
  have hrad : Fraction.le M (Fraction.mul (g (p.nodes k)) (g (p.nodes (k+1)))) :=
    Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative hleft R (Int.le_of_lt hbase))
      (Fraction.mul_le_mul_nonnegative_left hright (g (p.nodes k))
        (Int.le_of_lt (RadialSector.node_positive g p hg hbase k (by omega))))
  have hdet := Fraction.equiv_trans (TimeSubdivision.det_congr (hchart k (by omega)) (hchart (k+1) (by omega)))
    (RadialSector.ray_det _ _ _ _)
  have hdet0 : 0 ≤ (TimeSubdivision.det (q k).1 (q (k+1)).1).num :=
    Fraction.nonnegative_equiv hdet (Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_mul _ _
        (Int.le_of_lt (RadialSector.node_positive g p hg hbase k (by omega)))
        (Int.le_of_lt (RadialSector.node_positive g p hg hbase (k+1) (by omega)))) hW)
  have hlow : Fraction.le (Fraction.mul M W) (TimeSubdivision.det (q k).1 (q (k+1)).1).abs :=
    Fraction.le_equiv_right (Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative hrad W hW)
      (Fraction.equiv_symm hdet)) (Fraction.equiv_symm (Fraction.abs_of_nonnegative _ hdet0))
  have hstep := position_step_bound a (duration T j) V (remainder C T j) (q k) (q (k+1)) hv hres
  have hstep' : Fraction.le (pointDistance (q (k+1)).1 (q k).1)
      (Fraction.mul (Fraction.add V (Fraction.mul C T)) (duration T j)) := by
    apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans hstep
      (Fraction.add_le_add (remainder_le_width C T j hC hT)
        (Fraction.le_of_equiv (Fraction.mul_equiv_right V (Fraction.abs_of_nonnegative _ hT)))))
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
    ac_nf
  have hhigh := det_chord_bound _ _ P _ hP hp hstep'
  have hi := Fraction.mul_le_mul_nonnegative_left (Fraction.magnitudes.le_trans hlow hhigh)
    (TimeCalibration.inverse M hM) (Int.le_of_lt M.den_pos)
  have hcancel : Fraction.equiv (Fraction.mul (TimeCalibration.inverse M hM) (Fraction.mul M W)) W :=
    Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))
      (Fraction.equiv_trans (Fraction.mul_equiv_right W
        (Fraction.equiv_trans (Fraction.mul_comm _ _) (TimeCalibration.inverse_product M hM)))
        (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]))
  apply Fraction.le_equiv_right (Fraction.le_equiv_left (Fraction.equiv_symm hcancel) hi)
  simp only [slopeCoefficient,M,R,Fraction.equiv,Fraction.mul]
  ac_nf

/-- The sampled curve's slope mesh shrinks as a conclusion of its local
mechanical remainder, bounded velocities and positive monotone ray scale.
No force-polygon correspondence or shrinking mesh is assumed. -/
theorem radial_mesh_vanishes (a : Point → Point) (C T P V : Fraction)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (q : Nat → Nat → Point × Point)
    (hg : MonotoneRectangles.MonotoneOn g l r) (hbase : 0 < (g l).num)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num)
    (hcount : ∀ j, (parts j).count = blocks j)
    (hp : ∀ j k, k < blocks j → Fraction.le (pointNorm (q j k).1) P)
    (hv : ∀ j k, k < blocks j → Fraction.le (pointNorm (q j k).2) V)
    (hchart : ∀ j k, k ≤ (parts j).count → pointEquiv (q j k).1
      (RadialSector.ray (g ((parts j).nodes k)) ((parts j).nodes k)))
    (hres : ∀ j k, k < blocks j → Fraction.le
      (stateDistance (q j (k+1)) (cell a (duration T j) (q j k))) (remainder C T j)) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun j => MonotoneRectangles.maxWidth (parts j)) := by
  have hb (j : Nat) := (MonotoneRectangles.maxWidth_bounds (parts j)).2
    (Fraction.mul (slopeCoefficient (g l) P V C T hbase) (duration T j))
    (fun k hk => radial_width_bound a C T P V g (parts j) (q j) j k hk hg hbase hC hT hP
      (hp j k (by simpa only [hcount j] using hk)) (hv j k (by simpa only [hcount j] using hk))
      (hchart j) (hres j k (by simpa only [hcount j] using hk)))
  have hs := dyadic_scaled_vanishes _ T (slopeCoefficient_nonnegative (g l) P V C T hbase hP hV hC hT) hT
  intro eps heps
  obtain ⟨N,hN⟩ := hs eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (hb j) (hN j hj)⟩

/-- Samples of one independently supplied rational-time state curve. The
initial time uses the displayed zero so all refinements share the same state;
other grid times are `k*T/2^j`. These are the given curve's own samples;
their comparison with Newton's polygons is derived below. -/
def samples (u : Fraction → Point × Point) (T : Fraction) (j k : Nat) : Point × Point :=
  u (if k=0 then Fraction.ofInt 0 else countTime T j k)

theorem samples_initial (u : Fraction → Point × Point) (T : Fraction) (j : Nat) :
    samples u T j 0 = u (Fraction.ofInt 0) := rfl

theorem sum_half (f : Nat → Fraction) (n : Nat) :
    Fraction.equiv (sum (fun i => (f i).half) n) (sum f n).half := by
  induction n with
  | zero => simp only [sum,Fraction.half,Fraction.ofInt,Fraction.equiv,Int.zero_mul]
  | succ n ih =>
    apply Fraction.equiv_trans (Fraction.add_equiv_right _ ih)
    simp only [sum,Fraction.equiv,Fraction.add,Fraction.half,Int.add_mul,Int.mul_add]
    ac_nf

theorem areaSum_half_fan (p : Nat → Point) (n : Nat) :
    Fraction.equiv (SectorFan.areaSum p n) (fan p n).half := sum_half _ n

theorem half_difference (A B : Fraction) :
    Fraction.equiv (durationDifference A.half B.half).abs (durationDifference A B).abs.half := by
  have he : Fraction.equiv (durationDifference A.half B.half) (durationDifference A B).half := by
    simp only [durationDifference,HarmonicStability.negF,Fraction.equiv,Fraction.add,Fraction.half,
      Int.add_mul,Int.mul_add,Int.neg_mul]
    ac_nf
  exact Fraction.abs_equiv he

theorem half_le_self (A : Fraction) (hA : 0 ≤ A.num) : Fraction.le A.half A := by
  have hp := Int.mul_nonneg hA (Int.le_of_lt A.den_pos)
  simp only [Fraction.le,Fraction.half,show (2 : Int)=1+1 by rfl,Int.mul_add,Int.add_mul,Int.one_mul,Int.mul_one]
  omega

theorem vanishing_add (f g : Nat → Fraction)
    (hf : Exhaustion.VanishingDifference Fraction.magnitudes f)
    (hg : Exhaustion.VanishingDifference Fraction.magnitudes g) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun j => Fraction.add (f j) (g j)) := by
  intro eps heps
  obtain ⟨N,hN⟩ := Exhaustion.eventually_and (hf eps.half heps) (hg eps.half heps)
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_lt_le
    (Fraction.add_lt_add (hN j hj).1 (hN j hj).2) (Fraction.le_of_equiv (Fraction.half_add_self eps))⟩

/-- A zero absolute difference establishes equality of rational values,
without identifying the displayed numerator/denominator pairs. -/
theorem equiv_of_abs_difference_zero (A B : Fraction)
    (h : Fraction.equiv (durationDifference A B).abs (Fraction.ofInt 0)) : Fraction.equiv A B := by
  have hn : (durationDifference A B).num = 0 := by
    simp only [Fraction.equiv,Fraction.abs,Fraction.ofInt,Int.mul_one,Int.zero_mul,
      Int.ofNat_eq_zero,Int.natAbs_eq_zero] at h
    exact h
  simp only [durationDifference,HarmonicStability.negF,Fraction.add,Int.neg_mul] at hn
  unfold Fraction.equiv
  omega

/-- Independent mechanical/regularity conditions for a given state curve.
The force bound is at the recursively constructed polygon's arrivals; the
other two bounds concern the given curve's own samples. Polygon/sample
agreement is derived from these explicit premises; the area law additionally
needs a chart, a central force and the area rules. -/
structure Conditions (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) : Prop where
  remainder_nonnegative : 0 ≤ C.num
  time_nonnegative : 0 ≤ T.num
  comparison_nonnegative : 0 ≤ L.num
  force_nonnegative : 0 ≤ B.num
  position_nonnegative : 0 ≤ P.num
  velocity_nonnegative : 0 ≤ V.num
  force_comparison : ∀ p r, Fraction.le (pointDistance (a p) (a r)) (Fraction.mul L (pointDistance p r))
  local_remainder : ∀ j k, k < blocks j → Fraction.le
    (stateDistance (samples u T j (k+1)) (cell a (duration T j) (samples u T j k))) (remainder C T j)
  short_window : Fraction.le (Fraction.mul T (TimeCalibration.rate one L (by decide))) ⟨1,2,by decide⟩
  polygon_force_bound : ∀ j, BoundedIteration.BoundedSamples a (duration T j) (u zero) B (blocks j)
  curve_position_bound : ∀ j k, k < blocks j → Fraction.le (pointNorm (samples u T j k).1) P
  curve_velocity_bound : ∀ j k, k < blocks j → Fraction.le (pointNorm (samples u T j k).2) V

theorem polygon_position_bound (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j k : Nat) (hk : k ≤ blocks j) :
    Fraction.le (pointNorm (BoundedIteration.run a (duration T j) (u zero) k).1)
      (BoundedIteration.uniformPositionCap T (u zero) B) := by
  have htime : Fraction.le (BoundedIteration.time (duration T j) k) T :=
    Fraction.le_equiv_right (BoundedIteration.time_monotone (duration T j) d.time_nonnegative
      k (blocks j) hk) (blocks_duration T j)
  exact BoundedIteration.position_bound_at_time a (duration T j) (u zero) B T
    d.time_nonnegative d.force_nonnegative d.time_nonnegative k
    (fun i hi => d.polygon_force_bound j i (by omega)) htime

theorem polygon_position_cap_nonnegative (T B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hB : 0 ≤ B.num) :
    0 ≤ (BoundedIteration.uniformPositionCap T s B).num :=
  Fraction.nonnegative_add _ _ (pointNorm_nonnegative _)
    (Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hT (pointNorm_nonnegative _))
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hT hT) hB))

theorem sampled_agreement (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u) :
    ∀ eps, 0 < eps.num → ∃ N, ∀ j, N ≤ j → ∀ k, k ≤ blocks j →
      Fraction.lt (stateDistance (BoundedIteration.run a (duration T j) (u zero) k) (samples u T j k)) eps :=
  dyadic_sample_agreement a C T L (u zero) (samples u T) d.remainder_nonnegative
    d.time_nonnegative d.comparison_nonnegative (samples_initial u T) d.force_comparison d.local_remainder d.short_window

theorem sampled_fan_comparison (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun j =>
      (durationDifference (fan (fun k => (BoundedIteration.run a (duration T j) (u zero) k).1) (blocks j))
        (fan (fun k => (samples u T j k).1) (blocks j))).abs) :=
  dyadic_fan_comparison a C T L (BoundedIteration.uniformPositionCap T (u zero) B) P V
    (u zero) (samples u T) d.remainder_nonnegative d.time_nonnegative d.comparison_nonnegative
    (polygon_position_cap_nonnegative T B (u zero) d.time_nonnegative d.force_nonnegative)
    d.position_nonnegative d.velocity_nonnegative (samples_initial u T) d.force_comparison d.local_remainder
    d.short_window (fun j k hk => polygon_position_bound a C T L B P V u d j k (by omega))
    d.curve_position_bound d.curve_velocity_bound

/-- The filled sector swept by every rational-time point of the given curve
in `[0,T]`, including the times between dyadic samples. -/
def sweptSector (u : Fraction → Point × Point) (T : Fraction) (x : Point) : Prop :=
  ∃ t, Fraction.le (Fraction.ofInt 0) t ∧ Fraction.le t T ∧
    ∃ w, ConvexCover.UnitInterval w ∧ pointEquiv x (pointScale w (u t).1)

/-- A chart of the given curve's own samples. Its graph covers the full curve image in both directions; its nodes have
the equal-time sample count and the correct point values. It supplies no shrinking mesh,
force-polygon agreement, area conclusion or between-region estimate. -/
structure RadialChart (g : Fraction → Fraction) (l r T : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (u : Fraction → Point × Point) : Prop where
  monotone : MonotoneRectangles.MonotoneOn g l r
  positive : 0 < (g l).num
  count : ∀ j, (parts j).count = blocks j
  curve_points : ∀ t, Fraction.le (Fraction.ofInt 0) t → Fraction.le t T →
    ∃ theta, Fraction.le l theta ∧ Fraction.le theta r ∧
      pointEquiv (u t).1 (RadialSector.ray (g theta) theta)
  graph_points : ∀ theta, Fraction.le l theta → Fraction.le theta r →
    ∃ t, Fraction.le (Fraction.ofInt 0) t ∧ Fraction.le t T ∧
      pointEquiv (u t).1 (RadialSector.ray (g theta) theta)
  samples : ∀ j k, k ≤ (parts j).count → pointEquiv (MotionSampling.samples u T j k).1
    (RadialSector.ray (g ((parts j).nodes k)) ((parts j).nodes k))

theorem charted_sector (g : Fraction → Fraction) (l r T : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (u : Fraction → Point × Point)
    (chart : RadialChart g l r T parts u) (x : Point) :
    sweptSector u T x ↔ RadialSector.sector g l r x := by
  constructor
  · rintro ⟨t,ht0,htT,w,hw,he⟩
    obtain ⟨theta,hl,hr,hp⟩ := chart.curve_points t ht0 htT
    exact ⟨theta,hl,hr,w,hw,pointEquiv_trans he (pointScale_congr w hp)⟩
  · rintro ⟨theta,hl,hr,w,hw,he⟩
    obtain ⟨t,ht0,htT,hp⟩ := chart.graph_points theta hl hr
    exact ⟨t,ht0,htT,w,hw,pointEquiv_trans he (pointEquiv_symm (pointScale_congr w hp))⟩

theorem sampled_radial_mesh (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u) :
    Exhaustion.VanishingDifference Fraction.magnitudes (fun j => MonotoneRectangles.maxWidth (parts j)) :=
  radial_mesh_vanishes a C T P V g l r parts (samples u T) chart.monotone chart.positive
    d.remainder_nonnegative d.time_nonnegative d.position_nonnegative d.velocity_nonnegative
    chart.count d.curve_position_bound d.curve_velocity_bound chart.samples d.local_remainder

theorem areaSum_error_le_fan_error (p q : Nat → Point) (n : Nat) :
    Fraction.le (durationDifference (SectorFan.areaSum p n) (SectorFan.areaSum q n)).abs
      (durationDifference (fan p n) (fan q n)).abs :=
  Fraction.le_equiv_left (Fraction.equiv_trans
    (Fraction.abs_equiv (difference_congr (areaSum_half_fan p n) (areaSum_half_fan q n)))
    (half_difference (fan p n) (fan q n)))
    (half_le_self _ (Fraction.abs_num_nonnegative _))

theorem sampled_chord_area (g : Fraction → Fraction) (l r T : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (u : Fraction → Point × Point)
    (chart : RadialChart g l r T parts u) (j : Nat) :
    Fraction.equiv (SectorFan.areaSum (fun k => (samples u T j k).1) (blocks j))
      (RadialSector.chordArea g (parts j)) := by
  rw [← chart.count j]
  apply sum_congr_bounded
  intro k hk
  exact RationalIntervals.half_equiv (TimeSubdivision.det_congr
    (chart.samples j k (by omega)) (chart.samples j (k+1) (by omega)))

/-! Finite mechanical-polygon/sample-chord geometry. Source of these
coordinate statements: the original English statements and checked proofs
below, from the existing finite sample and convex enclosure results. This
records the derivations without claiming historical textual support or
discovery. The matched locus concerns two finite polygons; it is not the
between-region B of the given curve. Square budgets count overlaps and do
not assign an area to their union. -/

def chordRadiusCoefficient (C T V : Fraction) : Fraction :=
  Fraction.add V (Fraction.mul (Fraction.ofInt 3) (Fraction.mul C T))

def chordRadius (C T V : Fraction) (j : Nat) : Fraction :=
  Fraction.mul (chordRadiusCoefficient C T V) (duration T j)

def chordSquareBudget (C T V : Fraction) (j : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt 4) (Fraction.mul (chordRadius C T V j) (chordRadius C T V j))

def chordCoverBudget (C T V : Fraction) (j : Nat) : Fraction :=
  PolygonFanArea.sum (fun _ => chordSquareBudget C T V j) (blocks j)

theorem chordRadiusCoefficient_nonnegative (C T V : Fraction)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hV : 0 ≤ V.num) :
    0 ≤ (chordRadiusCoefficient C T V).num :=
  Fraction.nonnegative_add _ _ hV
    (Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hC hT))

/-- Project the derived state error to position, including the final vertex. -/
theorem sampled_position_error (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j k : Nat) (hk : k ≤ blocks j) :
    Fraction.le (pointDistance (BoundedIteration.run a (duration T j) (u zero) k).1
      (samples u T j k).1) (stateBudget C T j) :=
  Fraction.magnitudes.le_trans (position_distance_le_state _ _)
    (dyadic_sample_bound a C T L (u zero) (samples u T) d.remainder_nonnegative
      d.time_nonnegative d.comparison_nonnegative (samples_initial u T) d.force_comparison
      d.local_remainder d.short_window j k hk)

/-- Equal interpolation parameters on the two actual edges inherit the
endpoint error bound. No curve value between samples is used. -/
theorem sampled_chord_edge_bound (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j k : Nat) (hk : k < blocks j) (theta : Fraction) (htheta : ConvexCover.UnitInterval theta) :
    Fraction.le (pointDistance
      (ConvexCover.lerp theta (BoundedIteration.run a (duration T j) (u zero) k).1
        (BoundedIteration.run a (duration T j) (u zero) (k+1)).1)
      (ConvexCover.lerp theta (samples u T j k).1 (samples u T j (k+1)).1))
      (stateBudget C T j) :=
  ConvexCover.lerp_difference_bound theta htheta _ _ _ _ _
    (sampled_position_error a C T L B P V u d j k (by omega))
    (sampled_position_error a C T L B P V u d j (k+1) (by omega))

/-- The left sample's velocity and local residual bound the full chord. -/
theorem sampled_chord_step_bound (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j k : Nat) (hk : k < blocks j) :
    Fraction.le (pointDistance (samples u T j (k+1)).1 (samples u T j k).1)
      (Fraction.mul (Fraction.add V (Fraction.mul C T)) (duration T j)) := by
  have hb := position_step_bound a (duration T j) V (remainder C T j)
    (samples u T j k) (samples u T j (k+1))
    (d.curve_velocity_bound j k hk) (d.local_remainder j k hk)
  have he := Fraction.mul_equiv_right V (Fraction.abs_of_nonnegative (duration T j) d.time_nonnegative)
  apply Fraction.le_equiv_right (Fraction.magnitudes.le_trans hb
    (Fraction.add_le_add (remainder_le_width C T j d.remainder_nonnegative d.time_nonnegative)
      (Fraction.le_of_equiv he)))
  simp only [Fraction.equiv,Fraction.add,Fraction.mul]
  simp only [Int.add_mul,Int.mul_add]
  ac_nf

/-- One actual square encloses every point of a filled cell patch. Its
radius follows from the derived endpoint and sample-step bounds. -/
theorem sampled_filled_patch_square (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j k : Nat) (hk : k < blocks j) (theta mu lambda : Fraction)
    (htheta : ConvexCover.UnitInterval theta) (hmu : ConvexCover.UnitInterval mu)
    (hlambda : ConvexCover.UnitInterval lambda) :
    ConvexCover.SquareContains (samples u T j k).1 (chordRadius C T V j)
      (ConvexCover.filledPatch theta mu lambda
        (BoundedIteration.run a (duration T j) (u zero) k).1
        (BoundedIteration.run a (duration T j) (u zero) (k+1)).1
        (samples u T j k).1 (samples u T j (k+1)).1) := by
  let S := Fraction.mul (Fraction.add V (Fraction.mul C T)) (duration T j)
  have hS : 0 ≤ S.num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_add _ _ d.velocity_nonnegative
      (Fraction.nonnegative_mul _ _ d.remainder_nonnegative d.time_nonnegative)) d.time_nonnegative
  have hE := stateBudget_nonnegative C T j d.remainder_nonnegative d.time_nonnegative
  have hR : Fraction.equiv (Fraction.add (stateBudget C T j) S) (chordRadius C T V j) := by
    simp only [stateBudget,S,chordRadius,chordRadiusCoefficient,Fraction.equiv,Fraction.add,Fraction.mul,
      Fraction.ofInt,Int.add_mul,Int.mul_add]
    ac_nf
    simp only [← Int.mul_assoc]
    omega
  have heR : Fraction.le (stateBudget C T j) (chordRadius C T V j) :=
    Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hS) hR
  have hsR : Fraction.le S (chordRadius C T V j) :=
    Fraction.le_equiv_right (Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hE)
      (Fraction.add_comm _ _)) hR
  have hr : 0 ≤ (chordRadius C T V j).num := Fraction.nonnegative_equiv
    (Fraction.equiv_symm hR) (Fraction.nonnegative_add _ _ hE hS)
  apply ConvexCover.filledPatch_square theta mu lambda htheta hmu hlambda _ _ _ _ _ _
  · exact Fraction.magnitudes.le_trans (sampled_position_error a C T L B P V u d j k (by omega)) heR
  · exact Fraction.le_equiv_right (Fraction.magnitudes.le_trans (pointDistance_triangle _ _ _)
      (Fraction.add_le_add (sampled_position_error a C T L B P V u d j (k+1) (by omega))
        (sampled_chord_step_bound a C T L B P V u d j k hk))) hR
  · exact Fraction.le_equiv_left (pointDistance_self_zero _)
      (by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hr)
  · exact Fraction.magnitudes.le_trans (sampled_chord_step_bound a C T L B P V u d j k hk) hsR

/-- The matched patch is a special case of the filled patch. -/
theorem sampled_chord_patch_square (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j k : Nat) (hk : k < blocks j) (theta lambda : Fraction)
    (htheta : ConvexCover.UnitInterval theta) (hlambda : ConvexCover.UnitInterval lambda) :
    ConvexCover.SquareContains (samples u T j k).1 (chordRadius C T V j)
      (ConvexCover.matchedPatch theta lambda
        (BoundedIteration.run a (duration T j) (u zero) k).1
        (BoundedIteration.run a (duration T j) (u zero) (k+1)).1
        (samples u T j k).1 (samples u T j (k+1)).1) :=
  sampled_filled_patch_square a C T L B P V u d j k hk theta theta lambda htheta htheta hlambda

/-- The larger finite edge strip has the same shrinking square cover. This
is geometric inclusion in the square union, not inclusion of sector differences. -/
theorem sampled_filled_cover (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j : Nat) (x : Point) :
    ConvexCover.FilledRegion
      (fun k => (BoundedIteration.run a (duration T j) (u zero) k).1)
      (fun k => (samples u T j k).1) (blocks j) x →
    ConvexCover.SquareCover (fun k => (samples u T j k).1) (chordRadius C T V j) (blocks j) x := by
  rintro ⟨k,hk,theta,mu,lambda,htheta,hmu,hlambda,hx⟩
  exact ⟨k,hk,(ConvexCover.square_contains_congr _ _ hx).mpr
    (sampled_filled_patch_square a C T L B P V u d j k hk theta mu lambda htheta hmu hlambda)⟩

/-- Set inclusion for the whole finite matched locus, with one square for
each cell. Equivalent rational point representatives are included. -/
theorem sampled_chord_cover (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j : Nat) (x : Point) :
    ConvexCover.MatchedRegion
      (fun k => (BoundedIteration.run a (duration T j) (u zero) k).1)
      (fun k => (samples u T j k).1) (blocks j) x →
    ConvexCover.SquareCover (fun k => (samples u T j k).1) (chordRadius C T V j) (blocks j) x := by
  rintro ⟨k,hk,theta,lambda,htheta,hlambda,hx⟩
  exact ⟨k,hk,(ConvexCover.square_contains_congr _ _ hx).mpr
    (sampled_chord_patch_square a C T L B P V u d j k hk theta lambda htheta hlambda)⟩

/-- Summed side products of the actual covering squares. This is a cover
budget, with no claim of disjointness or assigned union area. -/
theorem chord_cover_budget_formula (C T V : Fraction) (j : Nat) :
    Fraction.equiv (chordCoverBudget C T V j)
      (Fraction.mul (Fraction.mul (Fraction.mul (Fraction.ofInt 4)
        (Fraction.mul (chordRadiusCoefficient C T V) (chordRadiusCoefficient C T V))) T)
        (duration T j)) := by
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant _ _)
  apply Fraction.equiv_trans (b := Fraction.mul (Fraction.mul (Fraction.ofInt 4)
    (Fraction.mul (chordRadiusCoefficient C T V) (chordRadiusCoefficient C T V)))
    (Fraction.mul (Fraction.mul (Fraction.ofInt (blocks j : Int)) (duration T j)) (duration T j)))
  · simp only [chordSquareBudget,chordRadius,Fraction.equiv,Fraction.mul]
    ac_nf
  · exact Fraction.equiv_trans
      (Fraction.mul_equiv_left _ (Fraction.mul_equiv_right _ (blocks_duration T j)))
      (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))

theorem chord_cover_budgets_vanish (C T V : Fraction)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hV : 0 ≤ V.num) :
    Exhaustion.VanishingDifference Fraction.magnitudes (chordCoverBudget C T V) := by
  have hK := chordRadiusCoefficient_nonnegative C T V hC hT hV
  let D := Fraction.mul (Fraction.mul (Fraction.ofInt 4)
    (Fraction.mul (chordRadiusCoefficient C T V) (chordRadiusCoefficient C T V))) T
  have hD : 0 ≤ D.num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hK hK)) hT
  have hv := dyadic_scaled_vanishes D T hD hT
  intro eps heps
  obtain ⟨N,hN⟩ := hv eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (chord_cover_budget_formula C T V j)) (hN j hj)⟩

/-! Terminal radial connectors. Source: the original English coordinate
statements and proofs here. These derive an actual finite triangle's area
and its exhaustion from the motion estimates, not a sector-difference
inclusion or an assigned area for the union of strips. -/

def terminalConnector (a : Point → Point) (T : Fraction)
    (u : Fraction → Point × Point) (j : Nat) : Point → Prop :=
  SectorFan.Triangle (BoundedIteration.run a (duration T j) (u zero) (blocks j)).1
    (samples u T j (blocks j)).1

def terminalConnectorArea (a : Point → Point) (T : Fraction)
    (u : Fraction → Point × Point) (j : Nat) : Fraction :=
  (det (BoundedIteration.run a (duration T j) (u zero) (blocks j)).1
    (samples u T j (blocks j)).1).abs.half

theorem terminal_connector_area (area : SectorFan.AreaRules) (a : Point → Point)
    (T : Fraction) (u : Fraction → Point × Point) (j : Nat) :
    area.HasArea (terminalConnector a T u j) (terminalConnectorArea a T u j) :=
  SectorFan.unsigned_triangle_area area _ _

/-- The terminal sample is not covered by the supplied left-sample position
cap. Instead use the derived mechanical position cap and endpoint error. -/
theorem terminal_connector_bound (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u) (j : Nat) :
    Fraction.le (terminalConnectorArea a T u j)
      (Fraction.mul (BoundedIteration.uniformPositionCap T (u zero) B) (stateBudget C T j)) := by
  apply Fraction.magnitudes.le_trans (half_le_self _ (Fraction.abs_num_nonnegative _))
  apply det_chord_bound _ _ _ _
    (polygon_position_cap_nonnegative T B (u zero) d.time_nonnegative d.force_nonnegative)
    (polygon_position_bound a C T L B P V u d j (blocks j) (Nat.le_refl _))
  exact Fraction.le_equiv_left (pointDistance_symm _ _)
    (sampled_position_error a C T L B P V u d j (blocks j) (Nat.le_refl _))

theorem terminal_connector_areas_vanish (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u) :
    Exhaustion.VanishingDifference Fraction.magnitudes (terminalConnectorArea a T u) := by
  let R := BoundedIteration.uniformPositionCap T (u zero) B
  let K := Fraction.mul R (Fraction.mul (Fraction.ofInt 2) (Fraction.mul C T))
  have hR := polygon_position_cap_nonnegative T B (u zero) d.time_nonnegative d.force_nonnegative
  have hK : 0 ≤ K.num := Fraction.nonnegative_mul _ _ hR
    (Fraction.nonnegative_mul _ _ (by decide)
      (Fraction.nonnegative_mul _ _ d.remainder_nonnegative d.time_nonnegative))
  obtain hv := dyadic_scaled_vanishes K T hK d.time_nonnegative
  intro eps heps
  obtain ⟨N,hN⟩ := hv eps heps
  refine ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt ?_ (hN j hj)⟩
  exact Fraction.le_equiv_right (terminal_connector_bound a C T L B P V u d j)
    (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))

/-! Half-plane control for the finite mechanical vertices. Source: the
coordinate argument below, derived from the chart's positive lower radius
and the already proved shrinking sample error. This adds no premise of
polygon agreement or arbitrary-time curve regularity. -/

theorem positive_first_of_near_lower (p q : Point) (r : Fraction)
    (hq : Fraction.le r q.1) (hd : Fraction.lt (pointDistance p q) r) :
    0 < p.1.num := by
  by_cases hpos : 0 < p.1.num
  · exact hpos
  apply False.elim
  have hp : 0 ≤ -p.1.num := by omega
  have hsub : Fraction.le q.1 (pointSub q p).1 := Fraction.le_add_nonnegative _ _ hp
  have hnorm : Fraction.le (pointSub q p).1.abs (pointDistance q p) :=
    Fraction.le_add_nonnegative _ _ (Fraction.abs_num_nonnegative _)
  have hr := Fraction.magnitudes.le_trans hq (Fraction.magnitudes.le_trans hsub
    (Fraction.magnitudes.le_trans (Fraction.le_abs _) hnorm))
  exact Fraction.magnitudes.lt_irrefl r (Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_equiv_right hr (pointDistance_symm _ _)) hd)

theorem sampled_first_lower (g : Fraction → Fraction) (l r T : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (u : Fraction → Point × Point)
    (chart : RadialChart g l r T parts u) (j k : Nat) (hk : k ≤ blocks j) :
    Fraction.le (g l) (samples u T j k).1.1 := by
  have hk' : k ≤ (parts j).count := by rw [chart.count]; exact hk
  have hb := MonotoneRectangles.node_bounds (parts j) k hk'
  exact Fraction.le_equiv_right
    (chart.monotone l ((parts j).nodes k) (Fraction.magnitudes.le_refl _) hb.1 hb.2)
    (Fraction.equiv_symm (chart.samples j k hk').1)

theorem polygon_eventually_positive (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u) :
    ∃ N, ∀ j, N ≤ j → ∀ k, k ≤ blocks j →
      0 < (BoundedIteration.run a (duration T j) (u zero) k).1.1.num := by
  obtain ⟨N,hN⟩ := state_budgets_vanish C T d.remainder_nonnegative d.time_nonnegative
    (g l) chart.positive
  exact ⟨N,fun j hj k hk => positive_first_of_near_lower _ _ (g l)
    (sampled_first_lower g l r T parts u chart j k hk)
    (Fraction.magnitudes.lt_of_le_lt (sampled_position_error a C T L B P V u d j k hk) (hN j hj))⟩

/-- The first cell has a common initial vertex. Triangle exchange therefore
derives its actual sector-difference inclusion in the existing shrinking
square or its endpoint radial connector. Local chart orientation remains
explicit; this does not propagate the inclusion across all later cells.
Source: this original finite coordinate derivation. -/
theorem initial_cell_difference_cover (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j : Nat) (x : Point)
    (h0 : 0 < (samples u T j 0).1.1.num) (h1 : 0 < (samples u T j 1).1.1.num)
    (hd : 0 ≤ (det (samples u T j 0).1 (samples u T j 1).1).num)
    (hx : SectorFan.Triangle (samples u T j 0).1 (samples u T j 1).1 x)
    (hn : ¬ SectorFan.Triangle
      (BoundedIteration.run a (duration T j) (u zero) 0).1
      (BoundedIteration.run a (duration T j) (u zero) 1).1 x) :
    ConvexCover.SquareContains (samples u T j 0).1 (chordRadius C T V j) x ∨
      SectorFan.Triangle (BoundedIteration.run a (duration T j) (u zero) 1).1
        (samples u T j 1).1 x := by
  have hk : 0 < blocks j := by unfold blocks; exact Nat.pow_pos (by decide)
  rcases TriangleExchange.exchange_positive (samples u T j 0).1 (samples u T j 1).1
      (BoundedIteration.run a (duration T j) (u zero) 1).1 x h0 h1 hd hx with hp | hp | hp
  · exact False.elim (hn hp)
  · obtain ⟨r,v,hr,hv,he⟩ := TriangleExchange.triangleAt_common_start_patch _ _ _ _ hp
    exact Or.inl ((ConvexCover.square_contains_congr _ _ he).mpr
      (sampled_chord_patch_square a C T L B P V u d j 0 hk r v hr hv))
  · exact Or.inr hp

end NewtonLimitDynamics.Polygon.MotionSampling
