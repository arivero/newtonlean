import BarrowLib.Polygon.MotionCurveCover
import BarrowLib.Polygon.UniformMotionChart
import BarrowLib.Polygon.QuadraticSector

/-! Finite square covers of the mechanical/given-curve between-region for a
nonmonotone radial chart with a supplied Lipschitz bound (newtonlean issue 3).

The monotone covers of `MotionCurveCover` bound each curve/chord collar cell by
the endpoint increment of the chart, which is a bounded-variation fact. A chart
that is only uniformly continuous gives no such square budget: a cap collar
cell of tolerance `ε` needs a square of radius about `ε + MΔθ`, so `N` cells
cost at least `N ε²`. A supplied Lipschitz bound `K` ties the tolerance to the
cell width, `ε = K w` with `w` the explicit slope-mesh bound
`slopeCoefficient(m) · T / 2ʲ`. Each cell of the cap collar then lies in a
square of radius `(3K(1+|l|+|r|) + M + m) w` around its left curve sample, and
the same `2ʲ⁺¹` squares as in `MotionCurveCover` cover the whole between-region
with budget `8 c² / 2ʲ → 0`.

The between-region and its assigned area stay distinct: the square union has a
constructed area under the existing translation-and-cut convention, while
existence of the between-region's own area remains a premise. Source: the
original English statements and checked finite derivations below, without
historical textual attribution or priority claims. The Lipschitz bound is an
explicit premise, not attributed to Newton.
-/

namespace NewtonLimitDynamics.Polygon.LipschitzCurveCover
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates MotionSampling
open HarmonicDyadic HarmonicTimeComparison PolygonFanArea UniformMotionChart

/-- A supplied Lipschitz bound `K` for `g` on `[l, r]`. -/
def LipschitzOn (g : Fraction → Fraction) (l r K : Fraction) : Prop :=
  ∀ s t, Fraction.le l s → Fraction.le s r → Fraction.le l t → Fraction.le t r →
    Fraction.le (durationDifference (g s) (g t)).abs (Fraction.mul K (durationDifference s t).abs)

private theorem abs_bound_iff (x c : Rat) (h : Rat.abs x ≤ c) : -c ≤ x ∧ x ≤ c := by
  simp only [Rat.abs] at h
  split at h <;> constructor <;> grind

/-- A Lipschitz graph is uniformly continuous, with `δ = ε / (2 (1 + K))`. -/
theorem uniform_of_lipschitz (g : Fraction → Fraction) (l r K : Fraction) (hK : 0 ≤ K.num)
    (h : LipschitzOn g l r K) : RationalBoundary.UniformOn (fun t => (t, g t)) l r := by
  intro eps heps
  have hepsR := (Fraction.positive_iff_toRat eps).mp heps
  have hKR := (Fraction.nonnegative_iff_toRat K).mp hK
  refine ⟨Fraction.ofRat ((eps.toRat / 2) / (1 + K.toRat)),
    (Fraction.positive_iff_toRat _).mpr (by
      rw [Fraction.toRat_ofRat]
      have h2 : 0 < 1 + K.toRat := by grind
      rw [Rat.div_def, Rat.div_def]
      exact Rat.mul_pos (Rat.mul_pos hepsR (Rat.inv_pos.mpr (by decide))) (Rat.inv_pos.mpr h2)),?_⟩
  intro s t hs0 hs1 ht0 ht1 hd
  have hL := (Fraction.le_iff_toRat _ _).mp (h s t hs0 hs1 ht0 ht1)
  have hdR := (Fraction.le_iff_toRat _ _).mp hd
  simp only [Fraction.toRat_abs, Fraction.toRat_durationDifference, Fraction.toRat_mul,
    Fraction.toRat_ofRat] at hL hdR
  apply (Fraction.lt_iff_toRat _ _).mpr
  have hneg (x : Fraction) : (⟨-x.num, x.den, x.den_pos⟩ : Fraction).toRat = -x.toRat :=
    Fraction.toRat_negF x
  simp only [FiniteEstimates.pointDistance, PointBounds.pointNorm, pointSub, pointAdd, pointNeg,
    Fraction.toRat_add, Fraction.toRat_abs, hneg]
  have e1 : Rat.abs (s.toRat + -t.toRat) = Rat.abs (t.toRat - s.toRat) := by
    rw [← Rat.sub_eq_add_neg, Rat.abs_sub_comm]
  have e2 : Rat.abs ((g s).toRat + -(g t).toRat) = Rat.abs ((g t).toRat - (g s).toRat) := by
    rw [← Rat.sub_eq_add_neg, Rat.abs_sub_comm]
  rw [e1, e2]
  have hw := Rat.mul_le_mul_of_nonneg_left hdR (show (0 : Rat) ≤ 1 + K.toRat by grind)
  have hfrac : (1 + K.toRat) * ((eps.toRat / 2) / (1 + K.toRat)) = eps.toRat / 2 := by
    have : (1 + K.toRat) ≠ 0 := by grind
    rw [Rat.mul_comm]
    exact Rat.div_mul_cancel this
  have := Rat.abs_nonneg (x := t.toRat - s.toRat)
  grind

/-- A bounded radial chart of the full curve image with a supplied Lipschitz bound. -/
structure LipschitzRadialChart (g : Fraction → Fraction) (l r T : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (u : Fraction → Point × Point)
    (m M K : Fraction) : Prop where
  lower_positive : 0 < m.num
  bounds : ∀ t, Fraction.le l t → Fraction.le t r → Fraction.le m (g t) ∧ Fraction.le (g t) M
  lipschitz_nonnegative : 0 ≤ K.num
  lipschitz : LipschitzOn g l r K
  count : ∀ j, (parts j).count = blocks j
  curve_points : ∀ t, Fraction.le (Fraction.ofInt 0) t → Fraction.le t T →
    ∃ theta, Fraction.le l theta ∧ Fraction.le theta r ∧
      pointEquiv (u t).1 (RadialSector.ray (g theta) theta)
  graph_points : ∀ theta, Fraction.le l theta → Fraction.le theta r →
    ∃ t, Fraction.le (Fraction.ofInt 0) t ∧ Fraction.le t T ∧
      pointEquiv (u t).1 (RadialSector.ray (g theta) theta)
  samples : ∀ j k, k ≤ (parts j).count → pointEquiv (MotionSampling.samples u T j k).1
    (RadialSector.ray (g ((parts j).nodes k)) ((parts j).nodes k))

variable {g : Fraction → Fraction} {l r T m M K : Fraction}
  {parts : Nat → MonotoneRectangles.Partition l r} {u : Fraction → Point × Point}

/-- Every Lipschitz chart is a bounded uniformly continuous chart. -/
theorem LipschitzRadialChart.toUniform (chart : LipschitzRadialChart g l r T parts u m M K) :
    UniformRadialChart g l r T parts u m M where
  lower_positive := chart.lower_positive
  bounds := chart.bounds
  uniform := uniform_of_lipschitz g l r K chart.lipschitz_nonnegative chart.lipschitz
  count := chart.count
  curve_points := chart.curve_points
  graph_points := chart.graph_points
  samples := chart.samples

/-- The upper bound of a chart is nonnegative. -/
theorem upper_nonnegative (chart : LipschitzRadialChart g l r T parts u m M K) : 0 ≤ M.num := by
  have hlr := UniformMotionChart.ordered (parts 0)
  have hb := chart.bounds l (Fraction.magnitudes.le_refl _) hlr
  exact Int.le_of_lt (RadialSector.positive_of_le _ _ chart.lower_positive
    (Fraction.magnitudes.le_trans hb.1 hb.2))

/-- Cell bounds from the Lipschitz bound: on a cell of width `Δ` with `K Δ ≤ ε`, the
chart lies between `g(θᵢ) - ε` and `g(θᵢ) + ε`, for either ordering of the endpoint
scales. -/
theorem cell_bounds (hK : 0 ≤ K.num) (hL : LipschitzOn g l r K)
    (p : MonotoneRectangles.Partition l r) (eps : Fraction) (i : Nat) (hi : i < p.count)
    (heps : Fraction.le (Fraction.mul K (MonotoneRectangles.width p i)) eps)
    (t : Fraction) (hl : Fraction.le (p.nodes i) t) (hr : Fraction.le t (p.nodes (i+1))) :
    Fraction.le (UniformRadialSector.lowerScales g p eps i) (g t) ∧
      Fraction.le (g t) (UniformRadialSector.upperScales g p eps i) := by
  have hn := MonotoneRectangles.node_bounds p i (by omega)
  have hn' := MonotoneRectangles.node_bounds p (i+1) (by omega)
  have ht : Fraction.le l t ∧ Fraction.le t r :=
    ⟨Fraction.magnitudes.le_trans hn.1 hl, Fraction.magnitudes.le_trans hr hn'.2⟩
  have hLR := (Fraction.le_iff_toRat _ _).mp (hL _ _ hn.1 hn.2 ht.1 ht.2)
  have hepsR := (Fraction.le_iff_toRat _ _).mp heps
  have hlR := (Fraction.le_iff_toRat _ _).mp hl
  have hrR := (Fraction.le_iff_toRat _ _).mp hr
  have hKR := (Fraction.nonnegative_iff_toRat K).mp hK
  simp only [Fraction.toRat_abs, Fraction.toRat_durationDifference, Fraction.toRat_mul,
    MonotoneRectangles.width] at hLR hepsR
  simp only [UniformRadialSector.lowerScales, UniformRadialSector.upperScales]
  constructor <;> apply (Fraction.le_iff_toRat _ _).mpr <;>
    simp only [Fraction.toRat_durationDifference, Fraction.toRat_add]
  all_goals
    rw [Rat.abs_of_nonneg (show 0 ≤ t.toRat - (p.nodes i).toRat by grind)] at hLR
    have hm := Rat.mul_le_mul_of_nonneg_left
      (show t.toRat - (p.nodes i).toRat ≤ (p.nodes (i+1)).toRat - (p.nodes i).toRat by grind) hKR
    have hb := abs_bound_iff _ _ (Rat.le_trans hLR (Rat.le_trans hm hepsR))
    grind

/-- Localize the actual curve/chord symmetric difference to one cap-collar cell. -/
theorem between_cell (p : MonotoneRectangles.Partition l r) (lo hi : Nat → Fraction)
    (hlo : ∀ i, i < p.count → 0 ≤ (lo i).num)
    (hpos : ∀ t, Fraction.le l t → Fraction.le t r → 0 < (g t).num)
    (hcell : ∀ i, i < p.count → ∀ t, Fraction.le (p.nodes i) t →
      Fraction.le t (p.nodes (i+1)) → Fraction.le (lo i) (g t) ∧ Fraction.le (g t) (hi i))
    (x : Point) (hx : RadialSector.between g p x) :
    ∃ k, k < p.count ∧
      SectorFan.Triangle (RadialSector.ray (hi k) (p.nodes k)) (RadialSector.ray (hi k) (p.nodes (k+1))) x ∧
      ¬ SectorFan.Triangle (RadialSector.ray (lo k) (p.nodes k))
        (RadialSector.ray (lo k) (p.nodes (k+1))) x := by
  obtain ⟨hLS,hSU,hLC,hCU⟩ := UniformRadialSector.strips_enclosure g p lo hi hlo hpos hcell
  have hup : RadialSector.strips p hi p.count x ∧ ¬ RadialSector.strips p lo p.count x := by
    rcases hx with ⟨hs,hc⟩ | ⟨hc,hs⟩
    · exact ⟨hSU x hs, fun h => hc (hLC x h)⟩
    · exact ⟨hCU x hc, fun h => hs (hLS x h)⟩
  obtain ⟨⟨k,hk,hxk⟩,hn⟩ := hup
  exact ⟨k,hk,hxk,fun h => hn ⟨k,hk,h⟩⟩

private theorem slope_abs_bound (t : Fraction) (hl : Fraction.le l t) (hr : Fraction.le t r) :
    Rat.abs t.toRat ≤ Rat.abs l.toRat + Rat.abs r.toRat := by
  have h1 := (Fraction.le_iff_toRat _ _).mp hl
  have h2 := (Fraction.le_iff_toRat _ _).mp hr
  simp only [Rat.abs]
  split <;> split <;> split <;> grind

private theorem duration_nonnegative (T : Fraction) (j : Nat) (hT : 0 ≤ T.num) :
    0 ≤ (duration T j).num := hT

/-- One cap-collar cell lies in an explicit L¹ ball around its left curve sample. -/
theorem cell_ball (p : MonotoneRectangles.Partition l r) (eps : Fraction) (k : Nat)
    (hk : k < p.count) (heps : 0 ≤ eps.num)
    (hlo : 0 < (UniformRadialSector.lowerScales g p eps k).num) (x : Point)
    (hu : SectorFan.Triangle
      (RadialSector.ray (UniformRadialSector.upperScales g p eps k) (p.nodes k))
      (RadialSector.ray (UniformRadialSector.upperScales g p eps k) (p.nodes (k+1))) x)
    (hl : ¬ SectorFan.Triangle
      (RadialSector.ray (UniformRadialSector.lowerScales g p eps k) (p.nodes k))
      (RadialSector.ray (UniformRadialSector.lowerScales g p eps k) (p.nodes (k+1))) x) :
    Fraction.le (pointNorm (pointSub x (RadialSector.ray (g (p.nodes k)) (p.nodes k))))
      (Fraction.add (Fraction.mul (Fraction.mul (Fraction.ofInt 3) eps)
          (Fraction.add (Fraction.ofInt 1) (p.nodes k).abs))
        (Fraction.mul (UniformRadialSector.upperScales g p eps k) (MonotoneRectangles.width p k))) := by
  have hRS : Fraction.le (UniformRadialSector.lowerScales g p eps k)
      (UniformRadialSector.upperScales g p eps k) := by
    apply (Fraction.le_iff_toRat _ _).mpr
    have := (Fraction.nonnegative_iff_toRat eps).mp heps
    simp only [UniformRadialSector.lowerScales, UniformRadialSector.upperScales,
      Fraction.toRat_durationDifference, Fraction.toRat_add]
    grind
  have hb := RadialCollarCover.triangle_collar_ball _ _ _ _ x (p.ordered k hk) hlo hRS hu hl
  have htri := ConvexCover.pointSub_triangle x
    (RadialSector.ray (UniformRadialSector.lowerScales g p eps k) (p.nodes k))
    (RadialSector.ray (g (p.nodes k)) (p.nodes k))
  apply Fraction.magnitudes.le_trans htri
  have hbR := (Fraction.le_iff_toRat _ _).mp hb
  apply (Fraction.le_iff_toRat _ _).mpr
  have hepsR := (Fraction.nonnegative_iff_toRat eps).mp heps
  have hneg (x : Fraction) : (⟨-x.num, x.den, x.den_pos⟩ : Fraction).toRat = -x.toRat :=
    Fraction.toRat_negF x
  simp only [Fraction.toRat_add, Fraction.toRat_mul, Fraction.toRat_durationDifference,
    Fraction.toRat_abs, Fraction.toRat_ofInt, UniformRadialSector.lowerScales,
    UniformRadialSector.upperScales, MonotoneRectangles.width] at hbR ⊢
  simp only [PointBounds.pointNorm, pointSub, pointAdd, pointNeg, RadialSector.ray,
    Fraction.toRat_add, Fraction.toRat_abs, hneg, Fraction.toRat_mul,
    Fraction.toRat_durationDifference] at hbR ⊢
  generalize (g (p.nodes k)).toRat = G at *
  generalize (p.nodes k).toRat = a at *
  generalize eps.toRat = e at *
  have h1 : Rat.abs (G - e + -G) = e := by
    rw [show G - e + -G = -e by grind, Rat.abs_neg, Rat.abs_of_nonneg hepsR]
  have h2 : Rat.abs ((G - e) * a + -(G * a)) = e * Rat.abs a := by
    rw [show (G - e) * a + -(G * a) = -(e * a) by grind, Rat.abs_neg]
    simp only [Rat.abs]
    split <;> split
    · rfl
    · have := Rat.mul_nonneg hepsR (show 0 ≤ -a by grind); grind
    · have := Rat.mul_nonneg hepsR (show 0 ≤ a by grind); grind
    · grind
  rw [h1, h2]
  grind

/-! The Lipschitz collar coefficient and the combined square cover. -/

/-- `(3K(1+|l|+|r|) + M + m) · slopeCoefficient(m)`. -/
def collarCoefficient (C T P V K m M l r : Fraction) (hm : 0 < m.num) : Fraction :=
  Fraction.mul (Fraction.add (Fraction.mul (Fraction.mul (Fraction.ofInt 3) K)
      (MotionCurveCover.slopeFactor l r)) (Fraction.add M m))
    (slopeCoefficient m P V C T hm)

def collarRadius (C T P V K m M l r : Fraction) (hm : 0 < m.num) (j : Nat) : Fraction :=
  Fraction.mul (collarCoefficient C T P V K m M l r hm) (duration T j)

/-- The per-partition cap tolerance `ε_j = K · slopeCoefficient(m) · T / 2ʲ`. -/
def tolerance (C T P V K m : Fraction) (hm : 0 < m.num) (j : Nat) : Fraction :=
  Fraction.mul K (Fraction.mul (slopeCoefficient m P V C T hm) (duration T j))

theorem collarCoefficient_nonnegative (C T P V K m M l r : Fraction) (hm : 0 < m.num)
    (hK : 0 ≤ K.num) (hM : 0 ≤ M.num) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num)
    (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    0 ≤ (collarCoefficient C T P V K m M l r hm).num :=
  Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ (by decide) hK)
        (MotionCurveCover.slopeFactor_nonnegative l r))
      (Fraction.nonnegative_add _ _ hM (Int.le_of_lt hm)))
    (slopeCoefficient_nonnegative m P V C T hm hP hV hC hT)

/-- Once `ε_j < m`, every collar cell of the chart's partition lies in the collar square
around its left sample. -/
theorem collar_cell_square (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : LipschitzRadialChart g l r T parts u m M K)
    (j : Nat) (hsmall : Fraction.lt (tolerance C T P V K m chart.lower_positive j) m)
    (k : Nat) (hk : k < (parts j).count) (x : Point)
    (hu : SectorFan.Triangle
      (RadialSector.ray (UniformRadialSector.upperScales g (parts j)
        (tolerance C T P V K m chart.lower_positive j) k) ((parts j).nodes k))
      (RadialSector.ray (UniformRadialSector.upperScales g (parts j)
        (tolerance C T P V K m chart.lower_positive j) k) ((parts j).nodes (k+1))) x)
    (hl : ¬ SectorFan.Triangle
      (RadialSector.ray (UniformRadialSector.lowerScales g (parts j)
        (tolerance C T P V K m chart.lower_positive j) k) ((parts j).nodes k))
      (RadialSector.ray (UniformRadialSector.lowerScales g (parts j)
        (tolerance C T P V K m chart.lower_positive j) k) ((parts j).nodes (k+1))) x) :
    ConvexCover.SquareContains (samples u T j k).1
      (collarRadius C T P V K m M l r chart.lower_positive j) x := by
  have hm := chart.lower_positive
  let e := tolerance C T P V K m hm j
  let w := Fraction.mul (slopeCoefficient m P V C T hm) (duration T j)
  have hkb : k < blocks j := by rw [← chart.count j]; exact hk
  have hnode := MonotoneRectangles.node_bounds (parts j) k (by omega)
  have hgk := chart.bounds _ hnode.1 hnode.2
  have hwidth : Fraction.le (MonotoneRectangles.width (parts j) k) w :=
    radial_width_bound_lower a C T P V g (parts j) (samples u T j) j k hk m hm
      (fun i hi => (chart.bounds _ (MonotoneRectangles.node_bounds (parts j) i hi).1
        (MonotoneRectangles.node_bounds (parts j) i hi).2).1)
      d.remainder_nonnegative d.time_nonnegative d.position_nonnegative
      (d.curve_position_bound j k hkb) (d.curve_velocity_bound j k hkb) (chart.samples j)
      (d.local_remainder j k hkb)
  have hw0 : 0 ≤ w.num := Fraction.nonnegative_mul _ _
    (slopeCoefficient_nonnegative m P V C T hm d.position_nonnegative d.velocity_nonnegative
      d.remainder_nonnegative d.time_nonnegative)
    (duration_nonnegative T j d.time_nonnegative)
  have he0 : 0 ≤ e.num := Fraction.nonnegative_mul _ _ chart.lipschitz_nonnegative hw0
  have hlo : 0 < (UniformRadialSector.lowerScales g (parts j) e k).num := by
    apply (Fraction.positive_iff_toRat _).mpr
    have h1 := (Fraction.le_iff_toRat _ _).mp hgk.1
    have h2 := (Fraction.lt_iff_toRat _ _).mp hsmall
    simp only [UniformRadialSector.lowerScales, Fraction.toRat_durationDifference]
    grind
  have hball := cell_ball (parts j) e k hk he0 hlo x hu hl
  apply ConvexCover.ball_inside_square
  apply Fraction.le_equiv_left (pointNorm_equiv (pointSub_congr
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (chart.samples j k (by omega))))
  apply Fraction.magnitudes.le_trans hball
  -- Bound 3e(1+|θ|) + (g + e) Δ by (3K(1+|l|+|r|) + M + m) w.
  have hsl := slope_abs_bound ((parts j).nodes k) hnode.1 hnode.2
  have hwR := (Fraction.le_iff_toRat _ _).mp hwidth
  have hw0R := (Fraction.nonnegative_iff_toRat w).mp hw0
  have hKR := (Fraction.nonnegative_iff_toRat K).mp chart.lipschitz_nonnegative
  have hgM := (Fraction.le_iff_toRat _ _).mp hgk.2
  have hgm := (Fraction.le_iff_toRat _ _).mp hgk.1
  have hem := (Fraction.lt_iff_toRat _ _).mp hsmall
  have hD0 : 0 ≤ (MonotoneRectangles.width (parts j) k).toRat :=
    (Fraction.nonnegative_iff_toRat _).mp ((difference_nonnegative_iff _ _).mpr ((parts j).ordered k hk))
  apply (Fraction.le_iff_toRat _ _).mpr
  have heR : e.toRat = K.toRat * w.toRat := Fraction.toRat_mul _ _
  have hcR : (collarRadius C T P V K m M l r hm j).toRat =
      (3 * K.toRat * (1 + (Rat.abs l.toRat + Rat.abs r.toRat)) + (M.toRat + m.toRat)) * w.toRat := by
    simp only [collarRadius, collarCoefficient, MotionCurveCover.slopeFactor, w,
      Fraction.toRat_add, Fraction.toRat_mul, Fraction.toRat_abs, Fraction.toRat_ofInt]
    grind
  simp only [Fraction.toRat_add, Fraction.toRat_mul, Fraction.toRat_abs, Fraction.toRat_ofInt,
    UniformRadialSector.upperScales, heR, hcR]
  rw [heR] at hem
  have hKw : 0 ≤ K.toRat * w.toRat := Rat.mul_nonneg hKR hw0R
  have t1 := Rat.mul_le_mul_of_nonneg_left
    (show 1 + Rat.abs ((parts j).nodes k).toRat ≤ 1 + (Rat.abs l.toRat + Rat.abs r.toRat) by grind)
    (show 0 ≤ 3 * (K.toRat * w.toRat) by grind)
  have t2 := Rat.mul_le_mul_of_nonneg_left hwR
    (show 0 ≤ (g ((parts j).nodes k)).toRat + K.toRat * w.toRat by grind)
  have t3 := Rat.mul_le_mul_of_nonneg_left
    (show (g ((parts j).nodes k)).toRat + K.toRat * w.toRat ≤ M.toRat + m.toRat by grind) hw0R
  grind

/-- Combined radius coefficient: the mechanical/sample part of `MotionSectorCover` plus
the Lipschitz collar coefficient times `T`. -/
def coefficient (C T B P V K m M l r : Fraction) (s : Point × Point) (hm : 0 < m.num) :
    Fraction :=
  Fraction.add (MotionSectorCover.coefficient C T B V s)
    (Fraction.mul (collarCoefficient C T P V K m M l r hm) T)

def radius (C T B P V K m M l r : Fraction) (s : Point × Point) (hm : 0 < m.num) (j : Nat) :
    Fraction :=
  duration (coefficient C T B P V K m M l r s hm) j

/-- The `2ʲ⁺¹` squares centred at the samples and at the terminal-triangle centres. -/
def cover (a : Point → Point) (C T B P V K m M l r : Fraction) (u : Fraction → Point × Point)
    (hm : 0 < m.num) (j : Nat) : Point → Prop :=
  ConvexCover.SquareCover (MotionSectorCover.centres a T u j)
    (radius C T B P V K m M l r (u (Fraction.ofInt 0)) hm j) (blocks (j+1))

/-- The summed square budget, counting overlaps. -/
def budget (C T B P V K m M l r : Fraction) (s : Point × Point) (hm : 0 < m.num) (j : Nat) :
    Fraction :=
  sum (fun _ => Fraction.mul (Fraction.ofInt 4)
    (Fraction.mul (radius C T B P V K m M l r s hm j) (radius C T B P V K m M l r s hm j)))
    (blocks (j+1))

theorem coefficient_nonnegative (C T B P V K m M l r : Fraction) (s : Point × Point)
    (hm : 0 < m.num) (hK : 0 ≤ K.num) (hM : 0 ≤ M.num) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num)
    (hB : 0 ≤ B.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    0 ≤ (coefficient C T B P V K m M l r s hm).num :=
  Fraction.nonnegative_add _ _
    (MotionSectorCover.coefficient_nonnegative C T B V s hC hT hB hV)
    (Fraction.nonnegative_mul _ _
      (collarCoefficient_nonnegative C T P V K m M l r hm hK hM hC hT hP hV) hT)

theorem radius_parts (C T B P V K m M l r : Fraction) (s : Point × Point) (hm : 0 < m.num)
    (j : Nat) :
    Fraction.equiv
      (Fraction.add (MotionSectorCover.radius C T B V s j) (collarRadius C T P V K m M l r hm j))
      (radius C T B P V K m M l r s hm j) := by
  simp only [MotionSectorCover.radius,collarRadius,radius,coefficient,duration,Fraction.equiv,
    Fraction.add,Fraction.mul,Int.add_mul]
  ac_nf

theorem mechanical_cover_inside (a : Point → Point) (C T B P V K m M l r : Fraction)
    (u : Fraction → Point × Point) (hm : 0 < m.num) (hK : 0 ≤ K.num) (hM : 0 ≤ M.num)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num)
    (j : Nat) (x : Point) (hx : MotionSectorCover.cover a C T B V u j x) :
    cover a C T B P V K m M l r u hm j x := by
  have hc : 0 ≤ (collarRadius C T P V K m M l r hm j).num := Fraction.nonnegative_mul _ _
    (collarCoefficient_nonnegative C T P V K m M l r hm hK hM hC hT hP hV) hT
  obtain ⟨k,hk,hx⟩ := hx
  exact ⟨k,hk,MotionSectorCover.square_radius_mono _ x
    (Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hc)
      (radius_parts C T B P V K m M l r _ hm j)) hx⟩

private theorem triangle_vertices_congr (p q v w x : Point)
    (hp : pointEquiv p v) (hq : pointEquiv q w) :
    SectorFan.Triangle p q x ↔ SectorFan.Triangle v w x := by
  constructor
  · rintro ⟨s,t,hs,ht,hst,hx⟩
    exact ⟨s,t,hs,ht,hst,pointEquiv_trans hx
      (pointAdd_congr (pointScale_congr s hp) (pointScale_congr t hq))⟩
  · rintro ⟨s,t,hs,ht,hst,hx⟩
    exact ⟨s,t,hs,ht,hst,pointEquiv_trans hx
      (pointAdd_congr (pointScale_congr s (pointEquiv_symm hp))
        (pointScale_congr t (pointEquiv_symm hq)))⟩

/-- The sample fan is the chart's chord figure. -/
theorem sampled_chord_region (chart : LipschitzRadialChart g l r T parts u m M K) (j : Nat)
    (x : Point) :
    SectorFan.Region (fun k => (samples u T j k).1) (blocks j) x ↔
      RadialSector.chordFigure g (parts j) x := by
  rw [← chart.count j]
  constructor
  · rintro ⟨k,hk,hx⟩
    exact ⟨k,hk,(triangle_vertices_congr _ _ _ _ x
      (chart.samples j k (by omega)) (chart.samples j (k+1) (by omega))).mp hx⟩
  · rintro ⟨k,hk,hx⟩
    exact ⟨k,hk,(triangle_vertices_congr _ _ _ _ x
      (chart.samples j k (by omega)) (chart.samples j (k+1) (by omega))).mpr hx⟩

/-- Once `ε_j < m`, the actual curve/chord symmetric difference lies in the cover. -/
theorem collar_cover_inside (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : LipschitzRadialChart g l r T parts u m M K)
    (j : Nat) (hsmall : Fraction.lt (tolerance C T P V K m chart.lower_positive j) m)
    (x : Point) (hx : RadialSector.between g (parts j) x) :
    cover a C T B P V K m M l r u chart.lower_positive j x := by
  have hm := chart.lower_positive
  let e := tolerance C T P V K m hm j
  have hpos (t : Fraction) (h1 : Fraction.le l t) (h2 : Fraction.le t r) : 0 < (g t).num :=
    RadialSector.positive_of_le _ _ hm (chart.bounds t h1 h2).1
  have hlo (i : Nat) (hi : i < (parts j).count) :
      0 ≤ (UniformRadialSector.lowerScales g (parts j) e i).num := by
    have hb := chart.bounds _ (MonotoneRectangles.node_bounds (parts j) i (by omega)).1
      (MonotoneRectangles.node_bounds (parts j) i (by omega)).2
    apply (Fraction.nonnegative_iff_toRat _).mpr
    have h1 := (Fraction.le_iff_toRat _ _).mp hb.1
    have h2 := (Fraction.lt_iff_toRat _ _).mp hsmall
    simp only [UniformRadialSector.lowerScales, Fraction.toRat_durationDifference]
    grind
  have hcell (i : Nat) (hi : i < (parts j).count) :=
    cell_bounds chart.lipschitz_nonnegative chart.lipschitz (parts j) e i hi (by
      have hib : i < blocks j := by rw [← chart.count j]; exact hi
      have hw := radial_width_bound_lower a C T P V g (parts j) (samples u T j) j i hi m hm
        (fun i hi => (chart.bounds _ (MonotoneRectangles.node_bounds (parts j) i hi).1
          (MonotoneRectangles.node_bounds (parts j) i hi).2).1)
        d.remainder_nonnegative d.time_nonnegative d.position_nonnegative
        (d.curve_position_bound j i hib) (d.curve_velocity_bound j i hib) (chart.samples j)
        (d.local_remainder j i hib)
      exact Fraction.mul_le_mul_nonnegative_left hw K chart.lipschitz_nonnegative)
  obtain ⟨k,hk,hu,hl⟩ := between_cell (parts j) _ _ hlo hpos hcell x hx
  have hsq := collar_cell_square a C L B P V d chart j hsmall k hk x hu hl
  have hmech : 0 ≤ (MotionSectorCover.radius C T B V (u (Fraction.ofInt 0)) j).num :=
    MotionSectorCover.coefficient_nonnegative C T B V _
      d.remainder_nonnegative d.time_nonnegative d.force_nonnegative d.velocity_nonnegative
  have hr := Fraction.le_equiv_right
    (Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hmech) (Fraction.add_comm _ _))
    (radius_parts C T B P V K m M l r (u (Fraction.ofInt 0)) hm j)
  change ConvexCover.SquareCover (MotionSectorCover.joinedCentres _ _ (blocks j)) _ (blocks (j+1)) x
  rw [blocks_succ,MotionSectorCover.joined_cover]
  exact Or.inl ⟨k,by rw [← chart.count j]; exact hk,MotionSectorCover.square_radius_mono _ x hr hsq⟩

private theorem difference_middle (P Q R : Prop) (h : (P ∧ ¬ R) ∨ (R ∧ ¬ P)) :
    ((P ∧ ¬ Q) ∨ (Q ∧ ¬ P)) ∨ ((Q ∧ ¬ R) ∨ (R ∧ ¬ Q)) := by
  by_cases hQ : Q
  · rcases h with ⟨hP,hnR⟩ | ⟨hR,hnP⟩
    · exact Or.inr (Or.inl ⟨hQ,hnR⟩)
    · exact Or.inl (Or.inr ⟨hQ,hnP⟩)
  · rcases h with ⟨hP,hnR⟩ | ⟨hR,hnP⟩
    · exact Or.inl (Or.inl ⟨hP,hQ⟩)
    · exact Or.inr (Or.inr ⟨hR,hQ⟩)

/-- Combine a mechanical/sample-sector inclusion with the Lipschitz collar at one level. -/
theorem between_cover_of_sector_cover (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : LipschitzRadialChart g l r T parts u m M K)
    (hM : 0 ≤ M.num) (j : Nat)
    (hsmall : Fraction.lt (tolerance C T P V K m chart.lower_positive j) m)
    (hsector : ∀ x, MotionSectorCover.sectorDifference a T u j x →
      MotionSectorCover.cover a C T B V u j x)
    (x : Point) (hx : MotionCurveCover.between a T u j x) :
    cover a C T B P V K m M l r u chart.lower_positive j x := by
  rcases difference_middle _
    (SectorFan.Region (fun k => (samples u T j k).1) (blocks j) x) _ hx with h | h
  · exact mechanical_cover_inside a C T B P V K m M l r u chart.lower_positive
      chart.lipschitz_nonnegative hM d.remainder_nonnegative d.time_nonnegative
      d.position_nonnegative d.velocity_nonnegative j x (hsector x h)
  · have hc : RadialSector.between g (parts j) x := by
      rcases h with ⟨hq,hnc⟩ | ⟨hc,hnq⟩
      · exact Or.inr ⟨(sampled_chord_region chart j x).mp hq,
          fun h => hnc ((UniformMotionChart.charted_sector chart.toUniform x).mpr h)⟩
      · exact Or.inl ⟨(UniformMotionChart.charted_sector chart.toUniform x).mp hc,
          fun h => hnq ((sampled_chord_region chart j x).mpr h)⟩
    exact collar_cover_inside a C L B P V d chart j hsmall x hc

/-- The tolerances `ε_j` vanish, so they eventually fall below `m`. -/
theorem tolerance_eventually_small (C T P V K m : Fraction) (hm : 0 < m.num)
    (hK : 0 ≤ K.num) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    ∃ N, ∀ j, N ≤ j → Fraction.lt (tolerance C T P V K m hm j) m := by
  have hv := dyadic_scaled_vanishes (Fraction.mul K (slopeCoefficient m P V C T hm)) T
    (Fraction.nonnegative_mul _ _ hK (slopeCoefficient_nonnegative m P V C T hm hP hV hC hT)) hT
  obtain ⟨N,hN⟩ := hv m hm
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))) (hN j hj)⟩

/-- Given the mechanical orientation, the full between-region is eventually covered. -/
theorem eventual_between_cover (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : LipschitzRadialChart g l r T parts u m M K)
    (hM : 0 ≤ M.num)
    (hdp : ∀ j k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num) :
    ∃ N, ∀ j, N ≤ j → ∀ x, MotionCurveCover.between a T u j x →
      cover a C T B P V K m M l r u chart.lower_positive j x := by
  obtain ⟨N₁,hN₁⟩ := UniformMotionChart.eventual_sector_difference_cover a C L B P V d
    chart.toUniform hdp
  obtain ⟨N₂,hN₂⟩ := tolerance_eventually_small C T P V K m chart.lower_positive
    chart.lipschitz_nonnegative d.remainder_nonnegative d.time_nonnegative
    d.position_nonnegative d.velocity_nonnegative
  exact ⟨max N₁ N₂,fun j hj => between_cover_of_sector_cover a C L B P V d chart hM j
    (hN₂ j (Nat.le_trans (Nat.le_max_right _ _) hj)) (hN₁ j (Nat.le_trans (Nat.le_max_left _ _) hj))⟩

theorem budget_formula (C T B P V K m M l r : Fraction) (s : Point × Point) (hm : 0 < m.num)
    (j : Nat) :
    Fraction.equiv (budget C T B P V K m M l r s hm j)
      (Fraction.mul (Fraction.mul (Fraction.ofInt 8)
        (Fraction.mul (coefficient C T B P V K m M l r s hm)
          (coefficient C T B P V K m M l r s hm)))
        (duration (Fraction.ofInt 1) j)) := by
  apply Fraction.equiv_trans (sum_constant _ _)
  simp only [radius,duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,blocks,
    Int.natCast_pow,Int.ofNat_two,Int.pow_succ,Int.one_mul,Int.mul_one]
  ac_nf
  have ht (z : Int) : 2 * (4 * z) = 8 * z := by omega
  rw [ht]

/-- The square budgets are `8 c² / 2ʲ` and vanish. -/
theorem budgets_vanish (C T B P V K m M l r : Fraction) (s : Point × Point) (hm : 0 < m.num)
    (hK : 0 ≤ K.num) (hM : 0 ≤ M.num) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hB : 0 ≤ B.num)
    (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    Exhaustion.VanishingDifference Fraction.magnitudes (budget C T B P V K m M l r s hm) := by
  have hc := coefficient_nonnegative C T B P V K m M l r s hm hK hM hC hT hB hP hV
  have hv := dyadic_scaled_vanishes
    (Fraction.mul (Fraction.ofInt 8)
      (Fraction.mul (coefficient C T B P V K m M l r s hm) (coefficient C T B P V K m M l r s hm)))
    (Fraction.ofInt 1)
    (Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hc hc)) (by decide)
  intro eps heps
  obtain ⟨N,hN⟩ := hv eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (budget_formula C T B P V K m M l r s hm j)) (hN j hj)⟩

/-- Under the explicit translation-and-cut convention the square unions have constructed
nonnegative areas below their budgets, and these areas vanish. The between-region's own
area is not constructed. -/
theorem cover_areas (area : TriangleContent.AreaRules) (a : Point → Point)
    (C T B P V K m M l r : Fraction) (u : Fraction → Point × Point) (hm : 0 < m.num)
    (hK : 0 ≤ K.num) (hM : 0 ≤ M.num) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hB : 0 ≤ B.num)
    (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (cover a C T B P V K m M l r u hm j) (A j) ∧ 0 ≤ (A j).num ∧
        Fraction.le (A j) (budget C T B P V K m M l r (u (Fraction.ofInt 0)) hm j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A := by
  have hc : ∀ j, ∃ A, area.HasArea (cover a C T B P V K m M l r u hm j) A ∧ 0 ≤ A.num ∧
      Fraction.le A (budget C T B P V K m M l r (u (Fraction.ofInt 0)) hm j) := by
    intro j
    exact BoxCoverArea.square_cover_area area (MotionSectorCover.centres a T u j)
      (radius C T B P V K m M l r (u (Fraction.ofInt 0)) hm j)
      (coefficient_nonnegative C T B P V K m M l r _ hm hK hM hC hT hB hP hV) (blocks (j+1))
  let A : Nat → Fraction := fun j => Classical.choose (hc j)
  have hA := fun j => Classical.choose_spec (hc j)
  refine ⟨A,hA,?_⟩
  intro eps heps
  obtain ⟨N,hN⟩ := budgets_vanish C T B P V K m M l r (u (Fraction.ofInt 0)) hm
    hK hM hC hT hB hP hV eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (hA j).2.2 (hN j hj)⟩

/-- Conditional decay of any separately assigned between-region areas from an eventual
cover. Existence of those areas stays a premise. -/
theorem assigned_between_areas_vanish_of_cover (area : TriangleContent.AreaRules)
    (a : Point → Point) (C L B P V : Fraction) (d : Conditions a C T L B P V u)
    (chart : LipschitzRadialChart g l r T parts u m M K) (hM : 0 ≤ M.num)
    (D : Nat → Fraction) (hD : ∀ j, area.HasArea (MotionCurveCover.between a T u j) (D j))
    (hcover : ∃ N, ∀ j, N ≤ j → ∀ x, MotionCurveCover.between a T u j x →
      cover a C T B P V K m M l r u chart.lower_positive j x) :
    (∀ j, 0 ≤ (D j).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes D := by
  obtain ⟨A,hA,hAv⟩ := cover_areas area a C T B P V K m M l r u chart.lower_positive
    chart.lipschitz_nonnegative hM d.remainder_nonnegative d.time_nonnegative
    d.force_nonnegative d.position_nonnegative d.velocity_nonnegative
  obtain ⟨N,hN⟩ := hcover
  refine ⟨fun j => RadialSector.assigned_area_nonnegative area.toSectorRules _ _ (hD j),?_⟩
  intro eps heps
  obtain ⟨N',hN'⟩ := hAv eps heps
  refine ⟨max N N',fun j hj => ?_⟩
  exact Fraction.magnitudes.lt_of_le_lt
    (area.monotone _ _ _ _ (hN j (Nat.le_trans (Nat.le_max_left _ _) hj)) (hD j) (hA j).1)
    (hN' j (Nat.le_trans (Nat.le_max_right _ _) hj))

/-- Any separately assigned areas of the actual mechanical/given-curve sector
differences are nonnegative and vanish, for a Lipschitz nonmonotone chart, given the
mechanical orientation. -/
theorem assigned_between_areas_vanish (area : TriangleContent.AreaRules)
    (a : Point → Point) (C L B P V : Fraction) (d : Conditions a C T L B P V u)
    (chart : LipschitzRadialChart g l r T parts u m M K)
    (hdp : ∀ j k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num)
    (D : Nat → Fraction) (hD : ∀ j, area.HasArea (MotionCurveCover.between a T u j) (D j)) :
    (∀ j, 0 ≤ (D j).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes D := by
  have hM := upper_nonnegative chart
  exact assigned_between_areas_vanish_of_cover area a C L B P V d chart hM D hD
    (eventual_between_cover a C L B P V d chart hM hdp)

/-! The nonmonotone quadratic control chart qualifies. -/

/-- The quadratic chart `g(θ) = 1 + θ - θ²` is Lipschitz with constant `1` on `[0,1]`:
`g(t) - g(s) = (t - s)(1 - s - t)` and `|1 - s - t| ≤ 1`. -/
theorem quadratic_lipschitz :
    LipschitzOn QuadraticSector.quadraticChart (Fraction.ofInt 0) (Fraction.ofInt 1)
      (Fraction.ofInt 1) := by
  intro s t hs0 hs1 ht0 ht1
  have hs0R := (Fraction.le_iff_toRat _ _).mp hs0
  have hs1R := (Fraction.le_iff_toRat _ _).mp hs1
  have ht0R := (Fraction.le_iff_toRat _ _).mp ht0
  have ht1R := (Fraction.le_iff_toRat _ _).mp ht1
  simp only [Fraction.toRat_ofInt] at hs0R hs1R ht0R ht1R
  apply (Fraction.le_iff_toRat _ _).mpr
  simp only [Fraction.toRat_abs, Fraction.toRat_durationDifference, Fraction.toRat_mul,
    Fraction.toRat_ofInt, QuadraticSector.chart_toRat]
  generalize s.toRat = a at *
  generalize t.toRat = b at *
  have hfac : (1 + b * (1 - b)) - (1 + a * (1 - a)) = (b - a) * (1 - a - b) := by grind
  rw [hfac]
  rcases Rat.le_total (a := 0) (b := b - a) with h | h
  · have u1 := Rat.mul_nonneg h (show (0:Rat) ≤ 1 - (1 - a - b) by grind)
    have u2 := Rat.mul_nonneg h (show (0:Rat) ≤ 1 + (1 - a - b) by grind)
    simp only [Rat.abs]
    split <;> (try split) <;> grind
  · have u1 := Rat.mul_nonneg (show (0:Rat) ≤ -(b - a) by grind)
      (show (0:Rat) ≤ 1 - (1 - a - b) by grind)
    have u2 := Rat.mul_nonneg (show (0:Rat) ≤ -(b - a) by grind)
      (show (0:Rat) ≤ 1 + (1 - a - b) by grind)
    simp only [Rat.abs]
    split <;> (try split) <;> grind

end NewtonLimitDynamics.Polygon.LipschitzCurveCover
