import BarrowLib.Polygon.ConvexCover
import ModernLib.Foundation.Polygon.SquareOuterContent
import ModernLib.Polygon.HarmonicUniform

/-!
Explicit finite square covers for matched pieces of the actual harmonic
coarse and fine polygonal paths. The square area is counted with multiplicity
over blocks. This is a geometric covering budget, not the area of the union
or the area between a polygon and a realized continuum trajectory. It is
separate from Kepler's centre-swept area.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicCover

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicRefinement
open HarmonicComparison
open HarmonicAccumulation
open HarmonicUniform
open PointBounds
open ConvexCover

private def two : Fraction := Fraction.ofInt 2
private def four : Fraction := Fraction.ofInt 4

def maxError (w h : Fraction) (s : Point × Point) (n : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt 3)
    (Fraction.mul (totalTime h n)
      (Fraction.mul h (Fraction.mul w.abs (stateNorm s))))

def halfDriftBudget (h : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul two (Fraction.mul h (stateNorm s))

def fullDriftBudget (h : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul four (Fraction.mul h (stateNorm s))

/-- The radius is `4hM + Emax`; this additive form makes the corner estimates
direct. `radius_formula` gives the equivalent compact expression. -/
def radius (w h : Fraction) (s : Point × Point) (n : Nat) : Fraction :=
  Fraction.add (fullDriftBudget h s) (maxError w h s n)

def squareArea (R : Fraction) : Fraction := SquareOuterContent.squareArea R

/-- Sum of `n` square areas, counted with multiplicity. -/
def coverBudget (w h : Fraction) (s : Point × Point) (n : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt (n : Int)) (squareArea (radius w h s n))

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem totalTime_nonnegative (h : Fraction) (n : Nat) (hh : 0 ≤ h.num) :
    0 ≤ (totalTime h n).num := by
  unfold totalTime Fraction.mul Fraction.ofInt
  exact Int.mul_nonneg (Int.mul_nonneg (by decide) (Int.natCast_nonneg _)) hh

-- Modern dependency score: 1/5 (M=1, H=4; transitive project theorems/axioms).
private theorem maxError_nonnegative (w h : Fraction) (s : Point × Point)
    (n : Nat) (hh : 0 ≤ h.num) : 0 ≤ (maxError w h s n).num :=
  Fraction.nonnegative_mul _ _ (by decide)
    (Fraction.nonnegative_mul _ _ (totalTime_nonnegative h n hh)
      (Fraction.nonnegative_mul _ _ hh
        (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w) (stateNorm_nonnegative s))))

-- Modern dependency score: 0/4 (M=0, H=4; transitive project theorems/axioms).
private theorem halfDriftBudget_nonnegative (h : Fraction) (s : Point × Point)
    (hh : 0 ≤ h.num) : 0 ≤ (halfDriftBudget h s).num :=
  Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hh (stateNorm_nonnegative s))

-- Modern dependency score: 0/4 (M=0, H=4; transitive project theorems/axioms).
private theorem fullDriftBudget_nonnegative (h : Fraction) (s : Point × Point)
    (hh : 0 ≤ h.num) : 0 ≤ (fullDriftBudget h s).num :=
  Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hh (stateNorm_nonnegative s))

-- Modern dependency score: 3/8 (M=3, H=5; transitive project theorems/axioms).
theorem radius_nonnegative (w h : Fraction) (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) : 0 ≤ (radius w h s n).num :=
  Fraction.nonnegative_add _ _ (fullDriftBudget_nonnegative h s hh)
    (maxError_nonnegative w h s n hh)

-- Modern dependency score: 1/2 (M=1, H=1; transitive project theorems/axioms).
theorem squareArea_nonnegative (R : Fraction) (hR : 0 ≤ R.num) :
    0 ≤ (squareArea R).num := SquareOuterContent.squareArea_nonnegative R hR

-- Modern dependency score: 6/11 (M=6, H=5; transitive project theorems/axioms).
theorem coverBudget_nonnegative (w h : Fraction) (s : Point × Point) (n : Nat)
    (hh : 0 ≤ h.num) : 0 ≤ (coverBudget w h s n).num :=
  Fraction.nonnegative_mul _ _ (Int.natCast_nonneg _)
    (squareArea_nonnegative _ (radius_nonnegative w h s n hh))

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem totalTime_le (h : Fraction) (i n : Nat)
    (hh : 0 ≤ h.num) (hin : i ≤ n) :
    Fraction.le (totalTime h i) (totalTime h n) := by
  have hi : (i : Int) ≤ (n : Int) := Int.ofNat_le.mpr hin
  have hcoef : 0 ≤ 2 * h.num * h.den :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) hh) (Int.le_of_lt h.den_pos)
  have hm := Int.mul_le_mul_of_nonneg_right hi hcoef
  unfold Fraction.le totalTime Fraction.mul Fraction.ofInt
  dsimp
  simp only [Int.one_mul]
  calc
    2 * (i : Int) * h.num * h.den ≤
        2 * (n : Int) * h.num * h.den := by
      calc
        _ = (i : Int) * (2 * h.num * h.den) := by ac_rfl
        _ ≤ (n : Int) * (2 * h.num * h.den) := hm
        _ = _ := by ac_rfl

/-- Every earlier actual endpoint error is bounded by the final-count cap. -/
-- Modern dependency score: 58/128 (M=58, H=70; transitive project theorems/axioms).
private theorem prefix_error_le_max (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i ≤ n)
    (hs : SmallTime w h n) :
    Fraction.le
      (stateNorm (stateSub (fineAt w h s i) (coarseAt w h s i)))
      (maxError w h s n) := by
  have hsmall := smallTime_prefix w h i n hh hin hs
  have he := actual_uniform_error w h s i hh hsmall
  have ht := totalTime_le h i n hh hin
  have hfactor : 0 ≤ (Fraction.mul h (Fraction.mul w.abs (stateNorm s))).num :=
    Fraction.nonnegative_mul _ _ hh
      (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w) (stateNorm_nonnegative s))
  have hm := Fraction.mul_le_mul_nonnegative ht
    (Fraction.mul h (Fraction.mul w.abs (stateNorm s))) hfactor
  have hm' := Fraction.mul_le_mul_nonnegative_left hm (Fraction.ofInt 3) (by decide)
  exact Fraction.magnitudes.le_trans he hm'

-- Modern dependency score: 0/25 (M=0, H=25; transitive project theorems/axioms).
private theorem drift_offset_le_state (d : Fraction) (hd : 0 ≤ d.num)
    (t : Point × Point) :
    Fraction.le
      (pointNorm (pointSub (pointAdd t.1 (pointScale d t.2)) t.1))
      (Fraction.mul d (stateNorm t)) := by
  have he := pointNorm_equiv (drift_offset d t.1 t.2)
  have hs := pointNorm_scale d t.2
  have hdabs := Fraction.abs_of_nonnegative d hd
  have hmul := Fraction.mul_equiv hdabs (Fraction.equiv_refl (pointNorm t.2))
  have hstart := Fraction.equiv_trans he (Fraction.equiv_trans hs hmul)
  have hv := velocity_le_state t
  have hm := Fraction.mul_le_mul_nonnegative_left hv d hd
  exact Fraction.le_equiv_left hstart hm

-- Modern dependency score: 0/5 (M=0, H=5; transitive project theorems/axioms).
private theorem two_le_four (h : Fraction) (s : Point × Point)
    (hh : 0 ≤ h.num) :
    Fraction.le (halfDriftBudget h s) (fullDriftBudget h s) := by
  have ht : Fraction.le two four := by
    unfold Fraction.le two four Fraction.ofInt
    decide
  exact Fraction.mul_le_mul_nonnegative ht (Fraction.mul h (stateNorm s))
    (Fraction.nonnegative_mul _ _ hh (stateNorm_nonnegative s))

-- Modern dependency score: 1/29 (M=1, H=28; transitive project theorems/axioms).
private theorem half_drift_le (h : Fraction) (s t : Point × Point)
    (hh : 0 ≤ h.num)
    (ht : Fraction.le (stateNorm t) (Fraction.mul two (stateNorm s))) :
    Fraction.le
      (pointNorm (pointSub (pointAdd t.1 (pointScale h t.2)) t.1))
      (halfDriftBudget h s) := by
  have h₀ := drift_offset_le_state h hh t
  have h₁ := Fraction.mul_le_mul_nonnegative_left ht h hh
  have hc := Fraction.magnitudes.le_trans h₀ h₁
  apply Fraction.le_equiv_right hc
  simp only [halfDriftBudget, two, Fraction.equiv, Fraction.mul, Fraction.ofInt]
  ac_nf

-- Modern dependency score: 1/30 (M=1, H=29; transitive project theorems/axioms).
private theorem full_drift_le (h : Fraction) (s t : Point × Point)
    (hh : 0 ≤ h.num)
    (ht : Fraction.le (stateNorm t) (Fraction.mul two (stateNorm s))) :
    Fraction.le
      (pointNorm (pointSub (pointAdd t.1 (pointScale (Fraction.add h h) t.2)) t.1))
      (fullDriftBudget h s) := by
  have hsum : 0 ≤ (Fraction.add h h).num :=
    Fraction.nonnegative_add h h hh hh
  have h₀ := drift_offset_le_state (Fraction.add h h) hsum t
  have h₁ := Fraction.mul_le_mul_nonnegative_left ht (Fraction.add h h) hsum
  have hc := Fraction.magnitudes.le_trans h₀ h₁
  apply Fraction.le_equiv_right hc
  simp only [fullDriftBudget, two, four, Fraction.equiv, Fraction.add,
    Fraction.mul, Fraction.ofInt]
  simp only [show (4 : Int) = 2 + 2 by rfl,
    Int.add_mul, Int.mul_add]
  ac_nf

def coarseStart (w h : Fraction) (s : Point × Point) (i : Nat) : Point :=
  (coarseAt w h s i).1

def fineStart (w h : Fraction) (s : Point × Point) (i : Nat) : Point :=
  (fineAt w h s i).1

/-- Position halfway along the actual coarse cell's inertial drift. This
vertex is a comparison subdivision; the coarse schedule has no impulse here. -/
def coarseMid (w h : Fraction) (s : Point × Point) (i : Nat) : Point :=
  (cell (linearField w) h (coarseAt w h s i)).1

def fineMid (w h : Fraction) (s : Point × Point) (i : Nat) : Point :=
  (cell (linearField w) h (fineAt w h s i)).1

def coarseEnd (w h : Fraction) (s : Point × Point) (i : Nat) : Point :=
  (coarseAt w h s (i + 1)).1

def fineEnd (w h : Fraction) (s : Point × Point) (i : Nat) : Point :=
  (fineAt w h s (i + 1)).1

-- Modern dependency score: 28/75 (M=28, H=47; transitive project theorems/axioms).
private theorem coarse_mid_le_half (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i ≤ n)
    (hs : SmallTime w h n) :
    Fraction.le (pointNorm (pointSub (coarseMid w h s i) (coarseStart w h s i)))
      (halfDriftBudget h s) :=
  half_drift_le h s (coarseAt w h s i) hh
    (coarse_state_le_two w h s i hh (smallTime_prefix w h i n hh hin hs))

-- Modern dependency score: 27/74 (M=27, H=47; transitive project theorems/axioms).
private theorem fine_mid_own_le_half (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i ≤ n)
    (hs : SmallTime w h n) :
    Fraction.le (pointNorm (pointSub (fineMid w h s i) (fineStart w h s i)))
      (halfDriftBudget h s) :=
  half_drift_le h s (fineAt w h s i) hh
    (fine_state_le_two w h s i hh (smallTime_prefix w h i n hh hin hs))

-- Modern dependency score: 28/75 (M=28, H=47; transitive project theorems/axioms).
private theorem coarse_end_le_full (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i ≤ n)
    (hs : SmallTime w h n) :
    Fraction.le (pointNorm (pointSub (coarseEnd w h s i) (coarseStart w h s i)))
      (fullDriftBudget h s) :=
  full_drift_le h s (coarseAt w h s i) hh
    (coarse_state_le_two w h s i hh (smallTime_prefix w h i n hh hin hs))

-- Modern dependency score: 59/129 (M=59, H=70; transitive project theorems/axioms).
private theorem fine_start_error_le (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i ≤ n)
    (hs : SmallTime w h n) :
    Fraction.le (pointNorm (pointSub (fineStart w h s i) (coarseStart w h s i)))
      (maxError w h s n) :=
  Fraction.magnitudes.le_trans
    (point_le_state (stateSub (fineAt w h s i) (coarseAt w h s i)))
    (prefix_error_le_max w h s i n hh hin hs)

-- Modern dependency score: 66/138 (M=66, H=72; transitive project theorems/axioms).
private theorem fine_mid_le (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i ≤ n)
    (hs : SmallTime w h n) :
    Fraction.le (pointNorm (pointSub (fineMid w h s i) (coarseStart w h s i)))
      (Fraction.add (maxError w h s n) (halfDriftBudget h s)) := by
  have ht := pointSub_triangle (fineMid w h s i) (fineStart w h s i)
    (coarseStart w h s i)
  have h₁ := fine_mid_own_le_half w h s i n hh hin hs
  have h₂ := fine_start_error_le w h s i n hh hin hs
  have hc := Fraction.magnitudes.le_trans ht (Fraction.add_le_add h₁ h₂)
  exact Fraction.le_equiv_right hc
    (Fraction.add_comm (halfDriftBudget h s) (maxError w h s n))

-- Modern dependency score: 68/140 (M=68, H=72; transitive project theorems/axioms).
private theorem fine_end_le (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i < n)
    (hs : SmallTime w h n) :
    Fraction.le (pointNorm (pointSub (fineEnd w h s i) (coarseStart w h s i)))
      (Fraction.add (maxError w h s n) (fullDriftBudget h s)) := by
  have hnext : i + 1 ≤ n := Nat.succ_le_of_lt hin
  have ht := pointSub_triangle (fineEnd w h s i) (coarseEnd w h s i)
    (coarseStart w h s i)
  have h₁ := fine_start_error_le w h s (i + 1) n hh hnext hs
  have h₂ := coarse_end_le_full w h s i n hh (Nat.le_of_lt hin) hs
  exact Fraction.magnitudes.le_trans ht (Fraction.add_le_add h₁ h₂)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem zero_le (R : Fraction) (hR : 0 ≤ R.num) :
    Fraction.le (Fraction.ofInt 0) R := by
  unfold Fraction.le Fraction.ofInt
  simpa using hR

/-- Six actual vertices, each measured from the coarse block start, fit in
the same coordinate L1 ball of radius `4hM + Emax`. The midpoint is only a
subdivision of the coarse drift; it receives no impulse. -/
-- Modern dependency score: 82/154 (M=82, H=72; transitive project theorems/axioms).
theorem actual_corners_in_ball (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i < n)
    (hs : SmallTime w h n) :
    let x := coarseStart w h s i
    let R := radius w h s n
    Fraction.le (pointNorm (pointSub x x)) R ∧
    Fraction.le (pointNorm (pointSub (coarseMid w h s i) x)) R ∧
    Fraction.le (pointNorm (pointSub (coarseEnd w h s i) x)) R ∧
    Fraction.le (pointNorm (pointSub (fineStart w h s i) x)) R ∧
    Fraction.le (pointNorm (pointSub (fineMid w h s i) x)) R ∧
    Fraction.le (pointNorm (pointSub (fineEnd w h s i) x)) R := by
  dsimp
  have hi : i ≤ n := Nat.le_of_lt hin
  have hE := maxError_nonnegative w h s n hh
  have hH := fullDriftBudget_nonnegative h s hh
  have hH2 := two_le_four h s hh
  have hHR : Fraction.le (fullDriftBudget h s) (radius w h s n) :=
    Fraction.le_add_nonnegative _ _ hE
  have hER : Fraction.le (maxError w h s n) (radius w h s n) :=
    Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hH)
      (Fraction.add_comm (maxError w h s n) (fullDriftBudget h s))
  have hsum : Fraction.le
      (Fraction.add (maxError w h s n) (halfDriftBudget h s))
      (radius w h s n) :=
    Fraction.le_equiv_right
      (Fraction.add_le_add_left hH2 (maxError w h s n))
      (Fraction.add_comm (maxError w h s n) (fullDriftBudget h s))
  have hlast : Fraction.equiv
      (Fraction.add (maxError w h s n) (fullDriftBudget h s))
      (radius w h s n) :=
    Fraction.add_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fraction.le_equiv_left (pointSub_self_zero _)
      (zero_le _ (radius_nonnegative w h s n hh))
  · exact Fraction.magnitudes.le_trans (coarse_mid_le_half w h s i n hh hi hs)
      (Fraction.magnitudes.le_trans hH2 hHR)
  · exact Fraction.magnitudes.le_trans (coarse_end_le_full w h s i n hh hi hs) hHR
  · exact Fraction.magnitudes.le_trans (fine_start_error_le w h s i n hh hi hs) hER
  · exact Fraction.magnitudes.le_trans (fine_mid_le w h s i n hh hi hs) hsum
  · exact Fraction.le_equiv_right (fine_end_le w h s i n hh hin hs) hlast

/-- The first matched patch compares the two paths over the first half-cell. -/
def firstPatch (w h : Fraction) (s : Point × Point) (i : Nat)
    (theta lambda : Fraction) : Point :=
  matchedPatch theta lambda (coarseStart w h s i) (coarseMid w h s i)
    (fineStart w h s i) (fineMid w h s i)

/-- The second matched patch compares the same second-half physical times. -/
def secondPatch (w h : Fraction) (s : Point × Point) (i : Nat)
    (theta lambda : Fraction) : Point :=
  matchedPatch theta lambda (coarseMid w h s i) (coarseEnd w h s i)
    (fineMid w h s i) (fineEnd w h s i)

-- Modern dependency score: 83/164 (M=83, H=81; transitive project theorems/axioms).
theorem firstPatch_square (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i < n)
    (hs : SmallTime w h n) (theta lambda : Fraction)
    (ht : UnitInterval theta) (hl : UnitInterval lambda) :
    SquareContains (coarseStart w h s i) (radius w h s n)
      (firstPatch w h s i theta lambda) := by
  obtain ⟨hc0, hc1, _, hf0, hf1, _⟩ := actual_corners_in_ball w h s i n hh hin hs
  exact matchedPatch_square theta lambda ht hl _ _ _ _ _ _ hc0 hc1 hf0 hf1

-- Modern dependency score: 83/164 (M=83, H=81; transitive project theorems/axioms).
theorem secondPatch_square (w h : Fraction) (s : Point × Point)
    (i n : Nat) (hh : 0 ≤ h.num) (hin : i < n)
    (hs : SmallTime w h n) (theta lambda : Fraction)
    (ht : UnitInterval theta) (hl : UnitInterval lambda) :
    SquareContains (coarseStart w h s i) (radius w h s n)
      (secondPatch w h s i theta lambda) := by
  obtain ⟨_, hc0, hc1, _, hf0, hf1⟩ := actual_corners_in_ball w h s i n hh hin hs
  exact matchedPatch_square theta lambda ht hl _ _ _ _ _ _ hc0 hc1 hf0 hf1

def shapeFactor (w h : Fraction) (n : Nat) : Fraction :=
  Fraction.add (Fraction.ofInt 4)
    (Fraction.mul (Fraction.ofInt 3) (Fraction.mul (totalTime h n) w.abs))

/-- Compact radius formula: `R=h*M*(4+3*T*|w|)`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem radius_formula (w h : Fraction) (s : Point × Point) (n : Nat) :
    Fraction.equiv (radius w h s n)
      (Fraction.mul (Fraction.mul h (stateNorm s)) (shapeFactor w h n)) := by
  simp only [radius, fullDriftBudget, maxError, shapeFactor, four,
    Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

/-- The summed square budget is `2*T*h*M²*(4+3*T*|w|)²`. It counts one
square per coarse block; no union-area or disjointness assertion is used. -/
-- Modern dependency score: 1/8 (M=1, H=7; transitive project theorems/axioms).
theorem coverBudget_formula (w h : Fraction) (s : Point × Point) (n : Nat) :
    Fraction.equiv (coverBudget w h s n)
      (Fraction.mul (Fraction.ofInt 2)
        (Fraction.mul (totalTime h n)
          (Fraction.mul h
            (Fraction.mul (Fraction.mul (stateNorm s) (stateNorm s))
              (Fraction.mul (shapeFactor w h n) (shapeFactor w h n)))))) := by
  let R := radius w h s n
  let Q := shapeFactor w h n
  let M := stateNorm s
  have hr := radius_formula w h s n
  have hsq := Fraction.mul_equiv hr hr
  have harea := Fraction.mul_equiv (Fraction.equiv_refl (Fraction.ofInt 4)) hsq
  have hbudget := Fraction.mul_equiv (Fraction.equiv_refl (Fraction.ofInt (n : Int))) harea
  apply Fraction.equiv_trans hbudget
  simp only [coverBudget, squareArea, R, Q, M, totalTime,
    Fraction.equiv, Fraction.mul, Fraction.ofInt]
  simp only [show (4 : Int) = 2 * 2 by rfl]
  ac_nf

private def one : Fraction := ⟨1, 1, by decide⟩
private def zero : Fraction := ⟨0, 1, by decide⟩
private def eighth : Fraction := ⟨1, 8, by decide⟩
private def quarter : Fraction := ⟨1, 4, by decide⟩
private def sample : Point × Point := ((one, zero), (zero, one))

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_small_time : SmallTime one eighth 1 := by
  unfold SmallTime Fraction.le
  decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_radius :
    Fraction.equiv (radius one eighth sample 1) ⟨19, 16, by decide⟩ := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_square_area :
    Fraction.equiv (squareArea (radius one eighth sample 1))
      ⟨361, 64, by decide⟩ := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_cover_budget :
    Fraction.equiv (coverBudget one eighth sample 1)
      ⟨361, 64, by decide⟩ := by decide

-- Modern dependency score: 84/156 (M=84, H=72; transitive project theorems/axioms).
theorem sample_all_corners :
    let x := coarseStart one eighth sample 0
    let R := radius one eighth sample 1
    Fraction.le (pointNorm (pointSub x x)) R ∧
    Fraction.le (pointNorm (pointSub (coarseMid one eighth sample 0) x)) R ∧
    Fraction.le (pointNorm (pointSub (coarseEnd one eighth sample 0) x)) R ∧
    Fraction.le (pointNorm (pointSub (fineStart one eighth sample 0) x)) R ∧
    Fraction.le (pointNorm (pointSub (fineMid one eighth sample 0) x)) R ∧
    Fraction.le (pointNorm (pointSub (fineEnd one eighth sample 0) x)) R :=
  actual_corners_in_ball one eighth sample 0 1 (by decide) (by decide) sample_small_time

-- Modern dependency score: 85/166 (M=85, H=81; transitive project theorems/axioms).
theorem sample_first_patch_square (theta lambda : Fraction)
    (ht : UnitInterval theta) (hl : UnitInterval lambda) :
    SquareContains (coarseStart one eighth sample 0) (radius one eighth sample 1)
      (firstPatch one eighth sample 0 theta lambda) :=
  firstPatch_square one eighth sample 0 1 (by decide) (by decide)
    sample_small_time theta lambda ht hl

-- Modern dependency score: 85/166 (M=85, H=81; transitive project theorems/axioms).
theorem sample_second_patch_square (theta lambda : Fraction)
    (ht : UnitInterval theta) (hl : UnitInterval lambda) :
    SquareContains (coarseStart one eighth sample 0) (radius one eighth sample 1)
      (secondPatch one eighth sample 0 theta lambda) :=
  secondPatch_square one eighth sample 0 1 (by decide) (by decide)
    sample_small_time theta lambda ht hl

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_zero_blocks_budget :
    Fraction.equiv (coverBudget one eighth sample 0) zero := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_zero_duration_budget :
    Fraction.equiv (coverBudget one zero sample 1) zero := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_quarter_ball_too_small :
    ¬ Fraction.le
      (pointNorm (pointSub (fineEnd one eighth sample 0)
        (coarseStart one eighth sample 0))) quarter := by
  unfold Fraction.le
  decide

/-- A separate coordinate-square control: the coarse endpoint's vertical
offset is 1/4, so a square of radius 1/8 cannot cover it. The preceding
L1-ball control does not assert failure of a square of radius 1/4. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_eighth_square_too_small :
    ¬ SquareContains (coarseStart one eighth sample 0) eighth
      (coarseEnd one eighth sample 0) := by
  unfold SquareContains Fraction.le
  decide

end NewtonLimitDynamics.Polygon.HarmonicCover
