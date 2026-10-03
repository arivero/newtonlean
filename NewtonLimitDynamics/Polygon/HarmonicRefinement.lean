import NewtonLimitDynamics.Polygon.HarmonicStability

/-!
Finite common-time comparison for the linear central field. The two actual
fine cells have duration `h`; the one actual coarse cell has duration `h+h`.
Their terminal positions need not agree. The directed connector from the fine
endpoint to the coarse endpoint closes a polygon comparison and is not a
mechanical cell. All statements are finite rational arithmetic. In particular,
this file constructs no limiting curve and makes no global area estimate.
Modern reconstruction motivated by the polygon arguments in De Motu
NATP00089 par9 / NATP00090 par17, 1687 NATP00077 par45 and 1713 NATP00082
par51. No historical edge between stages is inferred. The physical time and
inward-force readings require h>0 and w>0; the algebra also holds for signed
or zero parameters.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicRefinement

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability

def middle (w h : Fraction) (s : Point × Point) : Point :=
  (cell (linearField w) h s).1

def fine (w h : Fraction) (s : Point × Point) : Point × Point :=
  cell (linearField w) h (cell (linearField w) h s)

def coarse (w h : Fraction) (s : Point × Point) : Point × Point :=
  cell (linearField w) (Fraction.add h h) s

/-- The directed endpoint connector is `z → X`; it is bookkeeping only. -/
def connector (w h : Fraction) (s : Point × Point) : Point :=
  pointSub (coarse w h s).1 (fine w h s).1

/-- The fine endpoint is the coarse endpoint plus `-h² w y`. -/
theorem position_mismatch (w h : Fraction) (s : Point × Point) :
    pointEquiv (fine w h s).1
      (pointAdd (coarse w h s).1
        (pointScale (negF (Fraction.mul (Fraction.mul h h) w)) (middle w h s))) := by
  constructor <;>
    simp only [fine, coarse, middle, cell, linearField, negF, pointAdd,
      pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- Fine-minus-coarse velocity: `h² w v + h³ w² y`. -/
theorem velocity_mismatch (w h : Fraction) (s : Point × Point) :
    pointEquiv (fine w h s).2
      (pointAdd (coarse w h s).2
        (pointAdd (pointScale (Fraction.mul (Fraction.mul h h) w) s.2)
          (pointScale (Fraction.mul (Fraction.mul (Fraction.mul h h) h)
            (Fraction.mul w w)) (middle w h s)))) := by
  constructor <;>
    simp only [fine, coarse, middle, cell, linearField, negF, pointAdd,
      pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- Signed doubled area of the closed boundary `x → y → z → X → x`.
This is the area between the finite polygons, not either Kepler swept area. -/
def closedDefect (w h : Fraction) (s : Point × Point) : Fraction :=
  closedBoundaryTwice s.1 (middle w h s) (fine w h s).1 (coarse w h s).1

/-- The local closed boundary reduces to the single triangle `y,z,X`. -/
theorem closed_eq_triangle (w h : Fraction) (s : Point × Point) :
    Fraction.equiv (closedDefect w h s)
      (det (pointSub (fine w h s).1 (middle w h s))
        (pointSub (coarse w h s).1 (middle w h s))) := by
  simp only [closedDefect, closedBoundaryTwice, fine, coarse, middle, cell,
    linearField, negF, pointSub, pointNeg, pointAdd, pointScale, det,
    Fraction.equiv, Fraction.add, Fraction.mul,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- Exact cubic signed doubled gap for the common-time local refinement. -/
theorem closed_defect_cubic (w h : Fraction) (s : Point × Point) :
    Fraction.equiv (closedDefect w h s)
      (negF (Fraction.mul (Fraction.mul (Fraction.mul h h) h)
        (Fraction.mul w (det s.1 s.2)))) := by
  simp only [closedDefect, closedBoundaryTwice, fine, coarse, middle, cell,
    linearField, negF, pointAdd, pointScale, det,
    Fraction.equiv, Fraction.add, Fraction.mul,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- Nonnegative magnitude of this one closed signed triangle. It does not
account for overlaps or multiple lobes in a global polygon comparison. -/
def absoluteClosedGap (w h : Fraction) (s : Point × Point) : Fraction :=
  (closedDefect w h s).abs

theorem absoluteClosedGap_nonnegative (w h : Fraction) (s : Point × Point) :
    0 ≤ (absoluteClosedGap w h s).num := by
  exact Fraction.abs_num_nonnegative _

/-- Nonnegative local gap as the magnitude of the exact cubic coefficient.
    This is one triangle, so no cancellation of distinct lobes is involved. -/
theorem absolute_closed_defect_cubic (w h : Fraction) (s : Point × Point) :
    Fraction.equiv (absoluteClosedGap w h s)
      (Fraction.mul (Fraction.mul (Fraction.mul h h) h)
        (Fraction.mul w (det s.1 s.2))).abs :=
  Fraction.equiv_trans (Fraction.abs_equiv (closed_defect_cubic w h s))
    (Fraction.abs_neg _)

/-- Central-force Kepler sums agree for these two schedules. -/
theorem swept_equal (w h : Fraction) (s : Point × Point) :
    Fraction.equiv (swept (linearField w) [h, h] s)
      (swept (linearField w) [Fraction.add h h] s) := by
  simp only [swept, fine, coarse, middle, cell, linearField, negF,
    pointAdd, pointScale, det, Fraction.equiv, Fraction.add, Fraction.mul,
    Fraction.ofInt, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.mul_one, Int.one_mul, Int.zero_mul, Int.mul_zero] <;>
    ac_nf <;> omega

private def one : Fraction := ⟨1, 1, by decide⟩
private def zero : Fraction := ⟨0, 1, by decide⟩
private def half : Fraction := ⟨1, 2, by decide⟩
private def sample : Point × Point := ((one, zero), (zero, one))

theorem sample_middle : pointEquiv (middle one half sample) (one, half) := by decide
theorem sample_fine : pointEquiv (fine one half sample).1
    (⟨3, 4, by decide⟩, ⟨7, 8, by decide⟩) := by decide
theorem sample_coarse : pointEquiv (coarse one half sample).1 (one, one) := by decide
theorem sample_fine_swept : Fraction.equiv (swept (linearField one) [half, half] sample) one := by decide
theorem sample_coarse_swept : Fraction.equiv (swept (linearField one) [Fraction.add half half] sample) one := by decide
theorem sample_closed_defect : Fraction.equiv (closedDefect one half sample) ⟨-1, 8, by decide⟩ := by decide
theorem sample_absolute_closed_gap :
    Fraction.equiv (absoluteClosedGap one half sample) ⟨1, 8, by decide⟩ := by decide
theorem sample_closed_defect_nonzero :
    ¬ Fraction.equiv (closedDefect one half sample) zero := by decide

end NewtonLimitDynamics.Polygon.HarmonicRefinement
