import BarrowLib.Polygon.PointBounds
import BarrowLib.Polygon.ConvexCover

/-! Finite coordinate estimates for an arbitrary rational point map. The
coordinate L1 magnitude is a chosen algebraic gauge; no trajectory or force
law is asserted. -/

namespace NewtonLimitDynamics.Polygon.FiniteEstimates

open NewtonLimitDynamics
open TimeSubdivision
open PointBounds

def pointDistance (p q : Point) : Fraction := pointNorm (pointSub p q)

def stateDistance (s t : Point × Point) : Fraction :=
  Fraction.add (pointDistance s.1 t.1) (pointDistance s.2 t.2)

theorem pointNorm_le_distance_add (p q : Point) :
    Fraction.le (pointNorm p) (Fraction.add (pointDistance p q) (pointNorm q)) := by
  have he : pointEquiv p (pointAdd (pointSub p q) q) := by
    constructor <;> simp only [pointEquiv,pointSub,pointNeg,pointAdd,Fraction.equiv,
      Fraction.add,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega
  exact Fraction.le_equiv_left (pointNorm_equiv he) (pointNorm_add_le _ _)

/-- Reuse the generic point-subtraction triangle estimate. -/
theorem pointDistance_triangle (p q r : Point) :
    Fraction.le (pointDistance p r)
      (Fraction.add (pointDistance p q) (pointDistance q r)) :=
  ConvexCover.pointSub_triangle p q r

theorem pointDistance_symm (p q : Point) :
    Fraction.equiv (pointDistance p q) (pointDistance q p) := by
  have he : pointEquiv (pointSub p q) (pointNeg (pointSub q p)) := by
    constructor <;>
      simp only [pointEquiv, pointSub, pointNeg, pointAdd, Fraction.equiv,
        Fraction.add, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
      ac_nf <;> omega
  exact Fraction.equiv_trans (pointNorm_equiv he) (pointNorm_neg (pointSub q p))

theorem comparisonContract_reverse (a b : Point → Point) (L E : Fraction)
    (hc : ∀ p q, Fraction.le (pointDistance (a p) (b q))
      (Fraction.add (Fraction.mul L (pointDistance p q)) E)) :
    ∀ p q, Fraction.le (pointDistance (b p) (a q))
      (Fraction.add (Fraction.mul L (pointDistance p q)) E) := by
  intro p q
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_left (pointDistance_symm _ _) (hc q p))
    (Fraction.add_equiv (Fraction.mul_equiv_left L (pointDistance_symm q p))
      (Fraction.equiv_refl E))

/-- Triangle inequality for the coordinate distance of actual states. -/
theorem stateDistance_triangle (s t u : Point × Point) :
    Fraction.le (stateDistance s u)
      (Fraction.add (stateDistance s t) (stateDistance t u)) := by
  have hp := pointDistance_triangle s.1 t.1 u.1
  have hv := pointDistance_triangle s.2 t.2 u.2
  exact Fraction.le_equiv_right (Fraction.add_le_add hp hv) (by
    simp only [stateDistance, pointDistance, Fraction.equiv, Fraction.add,
      Int.add_mul, Int.mul_add]
    ac_nf)

theorem stateDistance_symm (s t : Point × Point) :
    Fraction.equiv (stateDistance s t) (stateDistance t s) :=
  Fraction.add_equiv (pointDistance_symm s.1 t.1) (pointDistance_symm s.2 t.2)

theorem pointDistance_self_zero (p : Point) :
    Fraction.equiv (pointDistance p p) (Fraction.ofInt 0) :=
  ConvexCover.pointSub_self_zero p

theorem stateDistance_self_zero (s : Point × Point) :
    Fraction.equiv (stateDistance s s) (Fraction.ofInt 0) :=
  Fraction.equiv_trans
    (Fraction.add_equiv (pointDistance_self_zero s.1) (pointDistance_self_zero s.2))
    (by simp [Fraction.equiv,Fraction.add,Fraction.ofInt])

theorem pointDistance_equiv {p p' q q' : Point}
    (hp : pointEquiv p p') (hq : pointEquiv q q') :
    Fraction.equiv (pointDistance p q) (pointDistance p' q') :=
  pointNorm_equiv (pointSub_congr hp hq)

/-- Drift to the sampled arrival point, then update velocity. -/
def cell (a : Point → Point) (h : Fraction) (s : Point × Point) : Point × Point :=
  let y := pointAdd s.1 (pointScale h s.2)
  (y, pointAdd s.2 (pointScale h (a y)))

/-- This cross-map contract permits additive sampling error `E`; neither
sampled map has to be exactly Lipschitz on its own. -/
def comparisonContract (a b : Point → Point) (L E : Fraction) : Prop :=
  ∀ p q, Fraction.le (pointDistance (a p) (b q))
    (Fraction.add (Fraction.mul L (pointDistance p q)) E)

private theorem point_difference_add (p q r t : Point) :
    pointEquiv (pointSub (pointAdd p r) (pointAdd q t))
      (pointAdd (pointSub p q) (pointSub r t)) := by
  constructor <;>
    simp only [pointEquiv, pointSub, pointNeg, pointAdd, Fraction.equiv,
      Fraction.add, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

private theorem point_difference_scale (h : Fraction) (p q : Point) :
    pointEquiv (pointSub (pointScale h p) (pointScale h q))
      (pointScale h (pointSub p q)) := by
  constructor <;>
    simp only [pointEquiv, pointSub, pointNeg, pointScale, pointAdd,
      Fraction.equiv, Fraction.add, Fraction.mul, Int.add_mul, Int.mul_add,
      Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

theorem difference_add_bound (p q r t : Point) :
    Fraction.le (pointDistance (pointAdd p r) (pointAdd q t))
      (Fraction.add (pointDistance p q) (pointDistance r t)) := by
  exact Fraction.le_equiv_left
    (pointNorm_equiv (point_difference_add p q r t))
    (pointNorm_add_le (pointSub p q) (pointSub r t))

theorem pointDistance_neg (p q : Point) :
    Fraction.equiv (pointDistance (pointNeg p) (pointNeg q)) (pointDistance p q) := by
  have he : pointEquiv (pointSub (pointNeg p) (pointNeg q)) (pointNeg (pointSub p q)) := by
    constructor <;>
      simp only [pointEquiv,pointSub,pointNeg,pointAdd,Fraction.equiv,Fraction.add,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.neg_neg] <;> ac_nf <;> omega
  exact Fraction.equiv_trans (pointNorm_equiv he) (pointNorm_neg (pointSub p q))

theorem difference_sub_bound (p q r t : Point) :
    Fraction.le (pointDistance (pointSub p r) (pointSub q t))
      (Fraction.add (pointDistance p q) (pointDistance r t)) :=
  Fraction.le_equiv_right (difference_add_bound p q (pointNeg r) (pointNeg t))
    (Fraction.add_equiv (Fraction.equiv_refl _) (pointDistance_neg r t))

theorem difference_scale (h : Fraction) (p q : Point) :
    Fraction.equiv (pointDistance (pointScale h p) (pointScale h q))
      (Fraction.mul h.abs (pointDistance p q)) :=
  Fraction.equiv_trans (pointNorm_equiv (point_difference_scale h p q))
    (pointNorm_scale h (pointSub p q))

def amplification (L h : Fraction) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.ofInt 1) h.abs)
    (Fraction.add (Fraction.ofInt 1) (Fraction.mul h.abs L))

/-- The excess in this coefficient bound is a sum of nonnegative products. -/
theorem component_amplification (P V H L E : Fraction)
    (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) (hH : 0 ≤ H.num) (hL : 0 ≤ L.num) :
    Fraction.le
      (Fraction.add (Fraction.add P (Fraction.mul H V))
        (Fraction.add V (Fraction.mul H
          (Fraction.add (Fraction.mul L (Fraction.add P (Fraction.mul H V))) E))))
      (Fraction.add
        (Fraction.mul (Fraction.mul (Fraction.add (Fraction.ofInt 1) H)
          (Fraction.add (Fraction.ofInt 1) (Fraction.mul H L))) (Fraction.add P V))
        (Fraction.mul H E)) := by
  let A := Fraction.add (Fraction.add P (Fraction.mul H V))
    (Fraction.add V (Fraction.mul H
      (Fraction.add (Fraction.mul L (Fraction.add P (Fraction.mul H V))) E)))
  let S := Fraction.add (Fraction.mul H P)
    (Fraction.add (Fraction.mul (Fraction.mul H L) V)
      (Fraction.mul (Fraction.mul (Fraction.mul H H) L) P))
  have hS : 0 ≤ S.num := Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ hH hP)
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hH hL) hV)
      (Fraction.nonnegative_mul _ _
        (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hH hH) hL) hP))
  apply Fraction.le_equiv_right (Fraction.le_add_nonnegative A S hS)
  simp only [A, S, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
    Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
  ac_nf

/-- Position growth of one triangular cell. -/
theorem cell_position_growth (a : Point → Point) (h : Fraction)
    (s : Point × Point) :
    Fraction.le (pointNorm (cell a h s).1)
      (Fraction.add (pointNorm s.1)
        (Fraction.mul h.abs (pointNorm s.2))) := by
  exact Fraction.le_equiv_right (pointNorm_add_le s.1 (pointScale h s.2))
    (Fraction.add_equiv (Fraction.equiv_refl _)
      (pointNorm_scale h s.2))

/-- Velocity growth under a bound at the sampled arrival point. -/
theorem cell_velocity_growth (a : Point → Point) (h B : Fraction)
    (s : Point × Point)
    (hB : Fraction.le (pointNorm (a (cell a h s).1)) B) :
    Fraction.le (pointNorm (cell a h s).2)
      (Fraction.add (pointNorm s.2) (Fraction.mul h.abs B)) := by
  have ha := pointNorm_add_le s.2 (pointScale h (a (cell a h s).1))
  have hs := pointNorm_scale h (a (cell a h s).1)
  have hm := Fraction.mul_le_mul_nonnegative_left hB h.abs
    (Fraction.abs_num_nonnegative h)
  exact Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right ha (Fraction.add_equiv (Fraction.equiv_refl _) hs))
    (Fraction.add_le_add_left hm (pointNorm s.2))

/-- A bounded acceleration gives finite one-cell state growth. -/
theorem cell_state_growth (a : Point → Point) (h B : Fraction)
    (s : Point × Point)
    (hB : Fraction.le (pointNorm (a (cell a h s).1)) B) :
    Fraction.le (stateNorm (cell a h s))
      (Fraction.add
        (Fraction.add (pointNorm s.1) (Fraction.mul h.abs (pointNorm s.2)))
        (Fraction.add (pointNorm s.2) (Fraction.mul h.abs B))) :=
  Fraction.add_le_add (cell_position_growth a h s)
    (cell_velocity_growth a h B s hB)

/-- Position perturbation keeps the arrival-point displacement visible. -/
theorem cell_position_perturbation (a b : Point → Point) (h : Fraction)
    (s t : Point × Point) :
    Fraction.le (pointDistance (cell a h s).1 (cell b h t).1)
      (Fraction.add (pointDistance s.1 t.1)
        (Fraction.mul h.abs (pointDistance s.2 t.2))) := by
  have hd := difference_add_bound s.1 t.1 (pointScale h s.2) (pointScale h t.2)
  exact Fraction.le_equiv_right hd
    (Fraction.add_equiv (Fraction.equiv_refl _)
      (difference_scale h s.2 t.2))

/-- Velocity perturbation for arbitrary sample maps. The term `|h|E`
cannot be dropped when the two maps differ at the same point. -/
theorem cell_velocity_perturbation_at (a b : Point → Point) (h L E : Fraction)
    (s t : Point × Point)
    (hc : Fraction.le (pointDistance (a (cell a h s).1) (b (cell b h t).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (cell a h s).1 (cell b h t).1)) E)) :
    Fraction.le (pointDistance (cell a h s).2 (cell b h t).2)
      (Fraction.add (pointDistance s.2 t.2)
        (Fraction.mul h.abs
          (Fraction.add (Fraction.mul L
            (pointDistance (cell a h s).1 (cell b h t).1)) E))) := by
  have hd := difference_add_bound s.2 t.2
    (pointScale h (a (cell a h s).1))
    (pointScale h (b (cell b h t).1))
  have hs := difference_scale h (a (cell a h s).1) (b (cell b h t).1)
  have hm := Fraction.mul_le_mul_nonnegative_left hc h.abs
    (Fraction.abs_num_nonnegative h)
  exact Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right hd (Fraction.add_equiv (Fraction.equiv_refl _) hs))
    (Fraction.add_le_add_left hm (pointDistance s.2 t.2))

theorem cell_velocity_perturbation (a b : Point → Point) (h L E : Fraction)
    (s t : Point × Point) (hc : comparisonContract a b L E) :
    Fraction.le (pointDistance (cell a h s).2 (cell b h t).2)
      (Fraction.add (pointDistance s.2 t.2)
        (Fraction.mul h.abs
          (Fraction.add (Fraction.mul L
            (pointDistance (cell a h s).1 (cell b h t).1)) E))) :=
  cell_velocity_perturbation_at a b h L E s t
    (hc (cell a h s).1 (cell b h t).1)

/-- The actual one-cell state perturbation with separate position and
velocity terms and the additive `|h|E` contribution. -/
theorem cell_state_perturbation_at (a b : Point → Point) (h L E : Fraction)
    (s t : Point × Point)
    (hc : Fraction.le (pointDistance (a (cell a h s).1) (b (cell b h t).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (cell a h s).1 (cell b h t).1)) E)) :
    Fraction.le (stateDistance (cell a h s) (cell b h t))
      (Fraction.add
        (Fraction.add (pointDistance s.1 t.1)
          (Fraction.mul h.abs (pointDistance s.2 t.2)))
        (Fraction.add (pointDistance s.2 t.2)
          (Fraction.mul h.abs
            (Fraction.add (Fraction.mul L
              (pointDistance (cell a h s).1 (cell b h t).1)) E)))) :=
  Fraction.add_le_add (cell_position_perturbation a b h s t)
    (cell_velocity_perturbation_at a b h L E s t hc)

theorem cell_state_perturbation (a b : Point → Point) (h L E : Fraction)
    (s t : Point × Point) (hc : comparisonContract a b L E) :
    Fraction.le (stateDistance (cell a h s) (cell b h t))
      (Fraction.add
        (Fraction.add (pointDistance s.1 t.1)
          (Fraction.mul h.abs (pointDistance s.2 t.2)))
        (Fraction.add (pointDistance s.2 t.2)
          (Fraction.mul h.abs
            (Fraction.add (Fraction.mul L
              (pointDistance (cell a h s).1 (cell b h t).1)) E)))) :=
  cell_state_perturbation_at a b h L E s t
    (hc (cell a h s).1 (cell b h t).1)

/-- Closed one-cell recurrence when `L` is nonnegative. This does not
assert a uniform mesh bound or any limiting trajectory. -/
theorem cell_state_perturbation_closed_at (a b : Point → Point)
    (h L E : Fraction) (s t : Point × Point)
    (hL : 0 ≤ L.num)
    (hc : Fraction.le (pointDistance (a (cell a h s).1) (b (cell b h t).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (cell a h s).1 (cell b h t).1)) E)) :
    Fraction.le (stateDistance (cell a h s) (cell b h t))
      (Fraction.add
        (Fraction.add (pointDistance s.1 t.1)
          (Fraction.mul h.abs (pointDistance s.2 t.2)))
        (Fraction.add (pointDistance s.2 t.2)
          (Fraction.mul h.abs
            (Fraction.add (Fraction.mul L
              (Fraction.add (pointDistance s.1 t.1)
                (Fraction.mul h.abs (pointDistance s.2 t.2)))) E)))) := by
  have hp := cell_position_perturbation a b h s t
  have hm := Fraction.mul_le_mul_nonnegative_left hp L hL
  have he := Fraction.add_le_add_right hm E
  have hh := Fraction.mul_le_mul_nonnegative_left he h.abs
    (Fraction.abs_num_nonnegative h)
  have hv := Fraction.add_le_add_left hh (pointDistance s.2 t.2)
  exact Fraction.magnitudes.le_trans (cell_state_perturbation_at a b h L E s t hc)
    (Fraction.add_le_add_left hv
      (Fraction.add (pointDistance s.1 t.1)
        (Fraction.mul h.abs (pointDistance s.2 t.2))))

theorem cell_state_perturbation_closed (a b : Point → Point)
    (h L E : Fraction) (s t : Point × Point)
    (hL : 0 ≤ L.num) (hc : comparisonContract a b L E) :
    Fraction.le (stateDistance (cell a h s) (cell b h t))
      (Fraction.add
        (Fraction.add (pointDistance s.1 t.1)
          (Fraction.mul h.abs (pointDistance s.2 t.2)))
        (Fraction.add (pointDistance s.2 t.2)
          (Fraction.mul h.abs
            (Fraction.add (Fraction.mul L
              (Fraction.add (pointDistance s.1 t.1)
                (Fraction.mul h.abs (pointDistance s.2 t.2)))) E)))) :=
  cell_state_perturbation_closed_at a b h L E s t hL
    (hc (cell a h s).1 (cell b h t).1)

/-- Finite Lipschitz amplification retains the oracle discrepancy explicitly. -/
theorem cell_amplification_at (a b : Point → Point) (h L E : Fraction)
    (s t : Point × Point) (hL : 0 ≤ L.num)
    (hc : Fraction.le (pointDistance (a (cell a h s).1) (b (cell b h t).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (cell a h s).1 (cell b h t).1)) E)) :
    Fraction.le (stateDistance (cell a h s) (cell b h t))
      (Fraction.add (Fraction.mul (amplification L h) (stateDistance s t))
        (Fraction.mul h.abs E)) :=
  Fraction.magnitudes.le_trans (cell_state_perturbation_closed_at a b h L E s t hL hc)
    (component_amplification _ _ _ _ _ (pointNorm_nonnegative _)
      (pointNorm_nonnegative _) (Fraction.abs_num_nonnegative _) hL)

theorem cell_amplification (a b : Point → Point) (h L E : Fraction)
    (s t : Point × Point) (hL : 0 ≤ L.num) (hc : comparisonContract a b L E) :
    Fraction.le (stateDistance (cell a h s) (cell b h t))
      (Fraction.add (Fraction.mul (amplification L h) (stateDistance s t))
        (Fraction.mul h.abs E)) :=
  cell_amplification_at a b h L E s t hL
    (hc (cell a h s).1 (cell b h t).1)

/-- The first and second half cells use the same sampled point map. -/
def twoHalf (a : Point → Point) (h : Fraction) (s : Point × Point) :
    Point × Point := cell a h (cell a h s)

def oneFull (a : Point → Point) (h : Fraction) (s : Point × Point) :
    Point × Point := cell a (Fraction.add h h) s

/-- Exact position defect of one full versus two half cells. It is the
first half-cell sample times `h²`, with no curve or adjacent-error premise. -/
theorem twoHalf_position_identity (a : Point → Point) (h : Fraction)
    (s : Point × Point) :
    pointEquiv (twoHalf a h s).1
      (pointAdd (oneFull a h s).1
        (pointScale (Fraction.mul h h) (a (cell a h s).1))) := by
  constructor <;>
    simp only [twoHalf, oneFull, cell, pointEquiv, pointAdd, pointScale,
      Fraction.equiv, Fraction.add, Fraction.mul, Int.add_mul, Int.mul_add] <;>
    ac_nf <;> omega

private theorem twoHalf_position_difference (a : Point → Point) (h : Fraction)
    (s : Point × Point) :
    pointEquiv (pointSub (twoHalf a h s).1 (oneFull a h s).1)
      (pointScale (Fraction.mul h h) (a (cell a h s).1)) := by
  constructor <;>
    simp only [twoHalf, oneFull, cell, pointEquiv, pointSub, pointNeg,
      pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- Local position error from a bound on the first sampled value. -/
theorem twoHalf_position_error (a : Point → Point) (h B : Fraction)
    (s : Point × Point)
    (hB : Fraction.le (pointNorm (a (cell a h s).1)) B) :
    Fraction.le (pointDistance (twoHalf a h s).1 (oneFull a h s).1)
      (Fraction.mul (Fraction.mul h h).abs B) := by
  have he := pointNorm_equiv (twoHalf_position_difference a h s)
  have hs := pointNorm_scale (Fraction.mul h h) (a (cell a h s).1)
  have hm := Fraction.mul_le_mul_nonnegative_left hB (Fraction.mul h h).abs
    (Fraction.abs_num_nonnegative _)
  exact Fraction.magnitudes.le_trans
    (Fraction.le_of_equiv (Fraction.equiv_trans he hs)) hm

private theorem first_to_full_difference (a : Point → Point) (h : Fraction)
    (s : Point × Point) :
    pointEquiv (pointSub (cell a h s).1 (oneFull a h s).1)
      (pointScale h (pointNeg s.2)) := by
  constructor <;>
    simp only [oneFull, cell, pointEquiv, pointSub, pointNeg, pointAdd,
      pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- The first half arrival and full arrival are separated by exactly one
drift of the initial velocity, measured in coordinate L1 magnitude. -/
theorem first_to_full_distance (a : Point → Point) (h : Fraction)
    (s : Point × Point) :
    Fraction.equiv (pointDistance (cell a h s).1 (oneFull a h s).1)
      (Fraction.mul h.abs (pointNorm s.2)) := by
  exact Fraction.equiv_trans
    (pointNorm_equiv (first_to_full_difference a h s))
    (Fraction.equiv_trans (pointNorm_scale h (pointNeg s.2))
      (Fraction.mul_equiv_left h.abs (pointNorm_neg s.2)))

/-- The exact velocity defect is the sum of two differences from the
full-cell sample. All three sample locations come from actual cells. -/
private theorem twoHalf_velocity_difference (a : Point → Point) (h : Fraction)
    (s : Point × Point) :
    pointEquiv (pointSub (twoHalf a h s).2 (oneFull a h s).2)
      (pointScale h
        (pointAdd
          (pointSub (a (cell a h s).1) (a (oneFull a h s).1))
          (pointSub (a (twoHalf a h s).1) (a (oneFull a h s).1)))) := by
  constructor <;>
    simp only [twoHalf, oneFull, cell, pointEquiv, pointSub, pointNeg,
      pointAdd, pointScale, Fraction.equiv, Fraction.add, Fraction.mul,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

/-- Two bounds at the actual sample locations suffice; no Lipschitz
coefficient is needed for this local identity and magnitude estimate. -/
theorem twoHalf_velocity_sample_error (a : Point → Point) (h E₁ E₂ : Fraction)
    (s : Point × Point)
    (h₁ : Fraction.le (pointDistance (a (cell a h s).1) (a (oneFull a h s).1)) E₁)
    (h₂ : Fraction.le (pointDistance (a (twoHalf a h s).1) (a (oneFull a h s).1)) E₂) :
    Fraction.le (pointDistance (twoHalf a h s).2 (oneFull a h s).2)
      (Fraction.mul h.abs (Fraction.add E₁ E₂)) := by
  let r₁ := pointSub (a (cell a h s).1) (a (oneFull a h s).1)
  let r₂ := pointSub (a (twoHalf a h s).1) (a (oneFull a h s).1)
  have he := pointNorm_equiv (twoHalf_velocity_difference a h s)
  have hs := pointNorm_scale h (pointAdd r₁ r₂)
  have ht := pointNorm_add_le r₁ r₂
  have hsum := Fraction.add_le_add h₁ h₂
  have hbound := Fraction.magnitudes.le_trans ht hsum
  have hm := Fraction.mul_le_mul_nonnegative_left hbound h.abs
    (Fraction.abs_num_nonnegative h)
  exact Fraction.magnitudes.le_trans
    (Fraction.le_of_equiv (Fraction.equiv_trans he hs)) hm

/-- Local velocity error for a sampled map with Lipschitz coefficient `L`
and additive discrepancy `E`. Rounded samples may have `E > 0`. -/
theorem twoHalf_velocity_error (a : Point → Point) (h L E : Fraction)
    (s : Point × Point) (hc : comparisonContract a a L E) :
    Fraction.le (pointDistance (twoHalf a h s).2 (oneFull a h s).2)
      (Fraction.mul h.abs
        (Fraction.add
          (Fraction.add (Fraction.mul L
            (pointDistance (cell a h s).1 (oneFull a h s).1)) E)
          (Fraction.add (Fraction.mul L
            (pointDistance (twoHalf a h s).1 (oneFull a h s).1)) E))) :=
  twoHalf_velocity_sample_error a h _ _ s
    (hc (cell a h s).1 (oneFull a h s).1)
    (hc (twoHalf a h s).1 (oneFull a h s).1)

/-- A fully explicit local velocity bound follows once the first sampled
value is bounded by `B` and the comparison coefficient is nonnegative. -/
theorem twoHalf_velocity_error_closed_at (a : Point → Point)
    (h L E B : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num)
    (hB : Fraction.le (pointNorm (a (cell a h s).1)) B)
    (h₁ : Fraction.le
      (pointDistance (a (cell a h s).1) (a (oneFull a h s).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (cell a h s).1 (oneFull a h s).1)) E))
    (h₂ : Fraction.le
      (pointDistance (a (twoHalf a h s).1) (a (oneFull a h s).1))
      (Fraction.add (Fraction.mul L
        (pointDistance (twoHalf a h s).1 (oneFull a h s).1)) E)) :
    Fraction.le (pointDistance (twoHalf a h s).2 (oneFull a h s).2)
      (Fraction.mul h.abs
        (Fraction.add
          (Fraction.add (Fraction.mul L
            (Fraction.mul h.abs (pointNorm s.2))) E)
          (Fraction.add (Fraction.mul L
            (Fraction.mul (Fraction.mul h h).abs B)) E))) := by
  have hd₁ : Fraction.le
      (pointDistance (cell a h s).1 (oneFull a h s).1)
      (Fraction.mul h.abs (pointNorm s.2)) :=
    Fraction.le_of_equiv (first_to_full_distance a h s)
  have hd₂ := twoHalf_position_error a h B s hB
  have hm₁ := Fraction.mul_le_mul_nonnegative_left hd₁ L hL
  have hm₂ := Fraction.mul_le_mul_nonnegative_left hd₂ L hL
  have he₁ := Fraction.add_le_add_right hm₁ E
  have he₂ := Fraction.add_le_add_right hm₂ E
  have hsum := Fraction.add_le_add he₁ he₂
  have htimes := Fraction.mul_le_mul_nonnegative_left hsum h.abs
    (Fraction.abs_num_nonnegative h)
  exact Fraction.magnitudes.le_trans
    (twoHalf_velocity_sample_error a h _ _ s h₁ h₂)
    htimes

theorem twoHalf_velocity_error_closed (a : Point → Point)
    (h L E B : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num)
    (hB : Fraction.le (pointNorm (a (cell a h s).1)) B)
    (hc : comparisonContract a a L E) :
    Fraction.le (pointDistance (twoHalf a h s).2 (oneFull a h s).2)
      (Fraction.mul h.abs
        (Fraction.add
          (Fraction.add (Fraction.mul L
            (Fraction.mul h.abs (pointNorm s.2))) E)
          (Fraction.add (Fraction.mul L
            (Fraction.mul (Fraction.mul h h).abs B)) E))) :=
  twoHalf_velocity_error_closed_at a h L E B s hL hB
    (hc (cell a h s).1 (oneFull a h s).1)
    (hc (twoHalf a h s).1 (oneFull a h s).1)

/-- Combined local state error; the two sampled arrival displacements remain
explicit so subsequent confinement estimates can be applied separately. -/
theorem twoHalf_state_error (a : Point → Point) (h L E B : Fraction)
    (s : Point × Point)
    (hB : Fraction.le (pointNorm (a (cell a h s).1)) B)
    (hc : comparisonContract a a L E) :
    Fraction.le (stateDistance (twoHalf a h s) (oneFull a h s))
      (Fraction.add
        (Fraction.mul (Fraction.mul h h).abs B)
        (Fraction.mul h.abs
          (Fraction.add
            (Fraction.add (Fraction.mul L
              (pointDistance (cell a h s).1 (oneFull a h s).1)) E)
            (Fraction.add (Fraction.mul L
              (pointDistance (twoHalf a h s).1 (oneFull a h s).1)) E)))) :=
  Fraction.add_le_add (twoHalf_position_error a h B s hB)
    (twoHalf_velocity_error a h L E s hc)

theorem twoHalf_state_error_closed (a : Point → Point)
    (h L E B : Fraction) (s : Point × Point)
    (hL : 0 ≤ L.num)
    (hB : Fraction.le (pointNorm (a (cell a h s).1)) B)
    (hc : comparisonContract a a L E) :
    Fraction.le (stateDistance (twoHalf a h s) (oneFull a h s))
      (Fraction.add
        (Fraction.mul (Fraction.mul h h).abs B)
        (Fraction.mul h.abs
          (Fraction.add
            (Fraction.add (Fraction.mul L
              (Fraction.mul h.abs (pointNorm s.2))) E)
            (Fraction.add (Fraction.mul L
              (Fraction.mul (Fraction.mul h h).abs B)) E)))) :=
  Fraction.add_le_add (twoHalf_position_error a h B s hB)
    (twoHalf_velocity_error_closed a h L E B s hL hB hc)

/-- Any represented zero duration leaves state values unchanged, for every map. -/
theorem zero_duration_cell (a : Point → Point) (h : Fraction)
    (hh : h.num = 0) (s : Point × Point) : stateEquiv (cell a h s) s := by
  constructor <;> constructor <;>
    simp only [cell,stateEquiv,pointEquiv,pointAdd,pointScale,Fraction.equiv,
      Fraction.add,Fraction.mul,hh,Int.zero_mul,Int.mul_zero,Int.add_zero] <;> ac_nf

private def controlZero : Fraction := Fraction.ofInt 0
private def controlHalf : Fraction := ⟨1, 2, by decide⟩
private def controlEighth : Fraction := ⟨1, 8, by decide⟩
private def controlState : Point × Point :=
  ((controlZero, controlZero), (controlZero, controlZero))
private def controlA : Point → Point := fun _ => (controlZero, ⟨-1, 1, by decide⟩)
private def controlB : Point → Point := fun _ => (controlZero, ⟨-2, 1, by decide⟩)
private def controlLinear : Point → Point := pointNeg
private def controlStart : Point × Point :=
  ((Fraction.ofInt 1, controlZero), (controlZero, Fraction.ofInt 1))

/-- Exact rational arithmetic pin for the pure map `p ↦ -p` at `h=1/8`. -/
theorem linear_sample_control :
    stateEquiv (cell controlLinear controlEighth controlStart)
      ((Fraction.ofInt 1, controlEighth),
        (⟨-1, 8, by decide⟩, ⟨63, 64, by decide⟩)) := by
  unfold stateEquiv
  decide

/-- Constant downward sample, zero initial state, and a half cell. -/
theorem constant_sample_control :
    stateEquiv (cell controlA controlHalf controlState)
      ((controlZero, controlZero),
        (controlZero, ⟨-1, 2, by decide⟩)) := by
  unfold stateEquiv
  decide

/-- Two unequal constant maps from the same zero state differ after a half
cell. This exact rational control detects omission of the sampling term. -/
theorem unequal_sample_control :
    Fraction.equiv
      (stateDistance (cell controlA controlHalf controlState)
        (cell controlB controlHalf controlState)) controlHalf := by
  decide

theorem unequal_sample_control_nonzero :
    ¬ Fraction.le
      (stateDistance (cell controlA controlHalf controlState)
        (cell controlB controlHalf controlState)) controlZero := by
  unfold Fraction.le
  decide

/-- Zero duration covers arbitrary maps and states. -/
theorem zero_duration_control (a : Point → Point) (s : Point × Point) :
    stateEquiv (cell a controlZero s) s :=
  zero_duration_cell a controlZero rfl s

end NewtonLimitDynamics.Polygon.FiniteEstimates
