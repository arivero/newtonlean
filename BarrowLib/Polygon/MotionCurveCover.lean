import BarrowLib.Polygon.MotionSectorCover
import BarrowLib.Polygon.RadialCollarCover

/-! Finite covers between a mechanical polygon sector and a given curve.
Source: the original English statements and checked coordinate derivations
below. These are project derivations without historical textual attribution
or priority claims. The motion estimates and full monotone radial chart
derive a square cover of the curve/chord collar. The mechanical/chord and
curve/chord covers therefore share the same explicit translation-and-cut
area convention. Area of the actual between-region is a separate obligation;
its area is not defined to be a cover budget.
-/

namespace NewtonLimitDynamics.Polygon.MotionCurveCover
open NewtonLimitDynamics TimeSubdivision PointBounds FiniteEstimates HarmonicStability
open HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization PolygonFanArea MotionSampling

private theorem abs_interval_bound (l r t : Fraction) (hl : Fraction.le l t)
    (hr : Fraction.le t r) : Fraction.le t.abs (Fraction.add l.abs r.abs) := by
  by_cases ht : 0 ≤ t.num
  · exact Fraction.le_equiv_left (Fraction.abs_of_nonnegative t ht)
      (Fraction.magnitudes.le_trans hr
        (Fraction.magnitudes.le_trans (Fraction.le_abs r)
          (Fraction.le_equiv_right
            (Fraction.le_add_nonnegative r.abs l.abs (Fraction.abs_num_nonnegative _))
            (Fraction.add_comm _ _))))
  · have hn : 0 ≤ (negF t).num := by change 0 ≤ -t.num; omega
    have hneg : Fraction.le (negF t) (negF l) := by
      simp only [Fraction.le,negF,Int.neg_mul] at hl ⊢
      omega
    have he : Fraction.equiv t.abs (negF t) := Fraction.equiv_trans
      (Fraction.equiv_symm (Fraction.abs_neg t)) (Fraction.abs_of_nonnegative _ hn)
    exact Fraction.le_equiv_left he
      (Fraction.magnitudes.le_trans hneg
        (Fraction.magnitudes.le_trans
          (Fraction.le_equiv_right (Fraction.le_abs (negF l)) (Fraction.abs_neg l))
          (Fraction.le_add_nonnegative l.abs r.abs (Fraction.abs_num_nonnegative _))))

def slopeFactor (l r : Fraction) : Fraction :=
  Fraction.add (Fraction.ofInt 1) (Fraction.add l.abs r.abs)

def collarCoefficient (C T P V : Fraction) (g : Fraction → Fraction) (l r : Fraction)
    (hbase : 0 < (g l).num) : Fraction :=
  Fraction.add (Fraction.mul (Fraction.add V (Fraction.mul C T)) (slopeFactor l r))
    (Fraction.mul (g r) (slopeCoefficient (g l) P V C T hbase))

def collarRadius (C T P V : Fraction) (g : Fraction → Fraction) (l r : Fraction)
    (hbase : 0 < (g l).num) (j : Nat) : Fraction :=
  Fraction.mul (collarCoefficient C T P V g l r hbase) (duration T j)

theorem slopeFactor_nonnegative (l r : Fraction) : 0 ≤ (slopeFactor l r).num :=
  Fraction.nonnegative_add _ _ (by decide)
    (Fraction.nonnegative_add _ _ (Fraction.abs_num_nonnegative _) (Fraction.abs_num_nonnegative _))

theorem collarCoefficient_nonnegative (C T P V : Fraction) (g : Fraction → Fraction)
    (l r : Fraction) (hbase : 0 < (g l).num) (hgr : 0 ≤ (g r).num)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    0 ≤ (collarCoefficient C T P V g l r hbase).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _
      (Fraction.nonnegative_add _ _ hV (Fraction.nonnegative_mul _ _ hC hT))
      (slopeFactor_nonnegative l r))
    (Fraction.nonnegative_mul _ _ hgr
      (slopeCoefficient_nonnegative (g l) P V C T hbase hP hV hC hT))

theorem chart_terminal_nonnegative (g : Fraction → Fraction) (l r T : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (u : Fraction → Point × Point)
    (chart : RadialChart g l r T parts u) : 0 ≤ (g r).num := by
  have hb := MonotoneRectangles.node_bounds (parts 0) 0 (by omega)
  have hlr := Fraction.magnitudes.le_trans hb.1 hb.2
  exact Int.le_of_lt (RadialSector.positive_of_le _ _ chart.positive
    (chart.monotone l r (Fraction.magnitudes.le_refl _) hlr (Fraction.magnitudes.le_refl _)))

private theorem sampled_radial_increment (g : Fraction → Fraction)
    {l r : Fraction} (p : MonotoneRectangles.Partition l r)
    (q : Nat → Point) (k : Nat) (hk : k < p.count)
    (hg : MonotoneRectangles.MonotoneOn g l r)
    (hq : ∀ i, i ≤ p.count → pointEquiv (q i) (RadialSector.ray (g (p.nodes i)) (p.nodes i))) :
    Fraction.le (durationDifference (g (p.nodes k)) (g (p.nodes (k+1))))
      (pointDistance (q (k+1)) (q k)) := by
  have hmono := hg _ _ (MonotoneRectangles.node_bounds p k (by omega)).1 (p.ordered k hk)
    (MonotoneRectangles.node_bounds p (k+1) (by omega)).2
  have he := (pointSub_congr (hq (k+1) (by omega)) (hq k (by omega))).1
  change Fraction.equiv (pointSub (q (k+1)) (q k)).1
    (durationDifference (g (p.nodes k)) (g (p.nodes (k+1)))) at he
  have heabs := Fraction.equiv_trans (Fraction.abs_equiv he)
    (Fraction.abs_of_nonnegative _ ((difference_nonnegative_iff _ _).mpr hmono))
  exact Fraction.le_equiv_left (Fraction.equiv_symm heabs)
    (Fraction.le_add_nonnegative _ _ (Fraction.abs_num_nonnegative _))

/-- Existing mechanical remainder and chart premises bound each actual
curve/chord collar cell by a square centred at its left curve sample.
The collar enclosure is derived from monotonicity, not supplied. -/
theorem collar_cell_square (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (j k : Nat) (hk : k < (parts j).count) (x : Point)
    (hu : SectorFan.Triangle
      (RadialSector.ray (g ((parts j).nodes (k+1))) ((parts j).nodes k))
      (RadialSector.ray (g ((parts j).nodes (k+1))) ((parts j).nodes (k+1))) x)
    (hl : ¬ SectorFan.Triangle
      (RadialSector.ray (g ((parts j).nodes k)) ((parts j).nodes k))
      (RadialSector.ray (g ((parts j).nodes k)) ((parts j).nodes (k+1))) x) :
    ConvexCover.SquareContains (samples u T j k).1
      (collarRadius C T P V g l r chart.positive j) x := by
  have hkb : k < blocks j := by rw [← chart.count j]; exact hk
  have hmono := chart.monotone _ _
    (MonotoneRectangles.node_bounds (parts j) k (by omega)).1 ((parts j).ordered k hk)
    (MonotoneRectangles.node_bounds (parts j) (k+1) (by omega)).2
  have hb := RadialCollarCover.triangle_collar_ball _ _ _ _ x ((parts j).ordered k hk)
    (RadialSector.node_positive g (parts j) chart.monotone chart.positive k (by omega)) hmono hu hl
  have hstep := sampled_chord_step_bound a C T L B P V u d j k hkb
  have hradial := Fraction.magnitudes.le_trans
    (sampled_radial_increment g (parts j) (fun i => (samples u T j i).1) k hk
      chart.monotone (chart.samples j)) hstep
  have hwidth := radial_width_bound a C T P V g (parts j) (samples u T j) j k hk
    chart.monotone chart.positive d.remainder_nonnegative d.time_nonnegative d.position_nonnegative
    (d.curve_position_bound j k hkb) (d.curve_velocity_bound j k hkb) (chart.samples j)
    (d.local_remainder j k hkb)
  have hleft := MonotoneRectangles.node_bounds (parts j) k (by omega)
  have hslope := Fraction.add_le_add_left (abs_interval_bound l r _ hleft.1 hleft.2)
    (Fraction.ofInt 1)
  have hright := MonotoneRectangles.node_bounds (parts j) (k+1) (by omega)
  have hgr := chart.monotone _ r hright.1 hright.2 (Fraction.magnitudes.le_refl _)
  have hdelta := (difference_nonnegative_iff _ _).mpr hmono
  have hW : 0 ≤ (MonotoneRectangles.width (parts j) k).num :=
    (difference_nonnegative_iff _ _).mpr ((parts j).ordered k hk)
  have hbound := Fraction.add_le_add
    (Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative_left hslope _ hdelta)
      (Fraction.mul_le_mul_nonnegative hradial _ (slopeFactor_nonnegative l r)))
    (Fraction.magnitudes.le_trans
      (Fraction.mul_le_mul_nonnegative hgr _ hW)
      (Fraction.mul_le_mul_nonnegative_left hwidth (g r)
        (chart_terminal_nonnegative g l r T parts u chart)))
  have hradius : Fraction.equiv
      (Fraction.add
        (Fraction.mul (Fraction.mul (Fraction.add V (Fraction.mul C T)) (duration T j)) (slopeFactor l r))
        (Fraction.mul (g r) (Fraction.mul (slopeCoefficient (g l) P V C T chart.positive) (duration T j))))
      (collarRadius C T P V g l r chart.positive j) := by
    simp only [collarRadius,collarCoefficient,Fraction.equiv,Fraction.add,Fraction.mul,
      Int.add_mul,Int.mul_add]
    ac_nf
  have hb' := Fraction.le_equiv_right (Fraction.magnitudes.le_trans hb hbound) hradius
  apply ConvexCover.ball_inside_square
  exact Fraction.le_equiv_left
    (pointNorm_equiv (pointSub_congr
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (chart.samples j k (by omega)))) hb'

theorem collar_square_cover (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (j : Nat) (x : Point) (hx : RadialSector.collar g (parts j) x) :
    ConvexCover.SquareCover (fun k => (samples u T j k).1)
      (collarRadius C T P V g l r chart.positive j) (blocks j) x := by
  obtain ⟨⟨k,hk,hu⟩,hl⟩ := hx
  refine ⟨k,by rw [← chart.count j]; exact hk,?_⟩
  exact collar_cell_square a C T L B P V u d g l r parts chart j k hk x hu
    (fun h => hl ⟨k,hk,h⟩)

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

theorem sampled_chord_region (g : Fraction → Fraction) (l r T : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (u : Fraction → Point × Point)
    (chart : RadialChart g l r T parts u) (j : Nat) (x : Point) :
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

def coefficient (C T B P V : Fraction) (s : Point × Point) (g : Fraction → Fraction)
    (l r : Fraction) (hbase : 0 < (g l).num) : Fraction :=
  Fraction.add (MotionSectorCover.coefficient C T B V s)
    (Fraction.mul (collarCoefficient C T P V g l r hbase) T)

def radius (C T B P V : Fraction) (s : Point × Point) (g : Fraction → Fraction)
    (l r : Fraction) (hbase : 0 < (g l).num) (j : Nat) : Fraction :=
  duration (coefficient C T B P V s g l r hbase) j

def cover (a : Point → Point) (C T B P V : Fraction) (u : Fraction → Point × Point)
    (g : Fraction → Fraction) (l r : Fraction) (hbase : 0 < (g l).num) (j : Nat) : Point → Prop :=
  ConvexCover.SquareCover (MotionSectorCover.centres a T u j)
    (radius C T B P V (u (Fraction.ofInt 0)) g l r hbase j) (blocks (j+1))

def budget (C T B P V : Fraction) (s : Point × Point) (g : Fraction → Fraction)
    (l r : Fraction) (hbase : 0 < (g l).num) (j : Nat) : Fraction :=
  sum (fun _ => Fraction.mul (Fraction.ofInt 4)
    (Fraction.mul (radius C T B P V s g l r hbase j) (radius C T B P V s g l r hbase j)))
    (blocks (j+1))

theorem coefficient_nonnegative (C T B P V : Fraction) (s : Point × Point)
    (g : Fraction → Fraction) (l r : Fraction) (hbase : 0 < (g l).num)
    (hgr : 0 ≤ (g r).num) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num)
    (hB : 0 ≤ B.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    0 ≤ (coefficient C T B P V s g l r hbase).num :=
  Fraction.nonnegative_add _ _
    (MotionSectorCover.coefficient_nonnegative C T B V s hC hT hB hV)
    (Fraction.nonnegative_mul _ _
      (collarCoefficient_nonnegative C T P V g l r hbase hgr hC hT hP hV) hT)

theorem radius_parts (C T B P V : Fraction) (s : Point × Point) (g : Fraction → Fraction)
    (l r : Fraction) (hbase : 0 < (g l).num) (j : Nat) :
    Fraction.equiv
      (Fraction.add (MotionSectorCover.radius C T B V s j) (collarRadius C T P V g l r hbase j))
      (radius C T B P V s g l r hbase j) := by
  simp only [MotionSectorCover.radius,collarRadius,radius,coefficient,duration,Fraction.equiv,
    Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
  ac_nf

theorem mechanical_cover_inside (a : Point → Point) (C T B P V : Fraction)
    (u : Fraction → Point × Point) (g : Fraction → Fraction) (l r : Fraction)
    (hbase : 0 < (g l).num) (hgr : 0 ≤ (g r).num)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num)
    (j : Nat) (x : Point) (hx : MotionSectorCover.cover a C T B V u j x) :
    cover a C T B P V u g l r hbase j x := by
  have hc : 0 ≤ (collarRadius C T P V g l r hbase j).num := Fraction.nonnegative_mul _ _
    (collarCoefficient_nonnegative C T P V g l r hbase hgr hC hT hP hV) hT
  obtain ⟨k,hk,hx⟩ := hx
  exact ⟨k,hk,MotionSectorCover.square_radius_mono _ x
    (Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hc)
      (radius_parts C T B P V _ g l r hbase j)) hx⟩

theorem collar_cover_inside (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (j : Nat) (x : Point) (hx : RadialSector.collar g (parts j) x) :
    cover a C T B P V u g l r chart.positive j x := by
  obtain ⟨k,hk,hx⟩ := collar_square_cover a C T L B P V u d g l r parts chart j x hx
  have hm : 0 ≤ (MotionSectorCover.radius C T B V (u (Fraction.ofInt 0)) j).num :=
    MotionSectorCover.coefficient_nonnegative C T B V _
      d.remainder_nonnegative d.time_nonnegative d.force_nonnegative d.velocity_nonnegative
  have hr := Fraction.le_equiv_right
    (Fraction.le_equiv_right (Fraction.le_add_nonnegative _ _ hm) (Fraction.add_comm _ _))
    (radius_parts C T B P V (u (Fraction.ofInt 0)) g l r chart.positive j)
  change ConvexCover.SquareCover (MotionSectorCover.joinedCentres _ _ (blocks j)) _ (blocks (j+1)) x
  rw [blocks_succ,MotionSectorCover.joined_cover]
  exact Or.inl ⟨k,hk,MotionSectorCover.square_radius_mono _ x hr hx⟩

/-- The actual filled between-region uses the mechanical polygon's sector
and the swept sector of every rational-time point of the given curve. It is
their symmetric difference, rather than an equal-parameter edge patch. -/
def between (a : Point → Point) (T : Fraction) (u : Fraction → Point × Point)
    (j : Nat) (x : Point) : Prop :=
  (SectorFan.Region
      (fun k => (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1) (blocks j) x ∧
    ¬ sweptSector u T x) ∨
  (sweptSector u T x ∧ ¬ SectorFan.Region
      (fun k => (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1) (blocks j) x)

private theorem difference_middle (P Q R : Prop) (h : (P ∧ ¬ R) ∨ (R ∧ ¬ P)) :
    ((P ∧ ¬ Q) ∨ (Q ∧ ¬ P)) ∨ ((Q ∧ ¬ R) ∨ (R ∧ ¬ Q)) := by
  by_cases hQ : Q
  · rcases h with ⟨hP,hnR⟩ | ⟨hR,hnP⟩
    · exact Or.inr (Or.inl ⟨hQ,hnR⟩)
    · exact Or.inl (Or.inr ⟨hQ,hnP⟩)
  · rcases h with ⟨hP,hnR⟩ | ⟨hR,hnP⟩
    · exact Or.inl (Or.inl ⟨hP,hQ⟩)
    · exact Or.inr (Or.inr ⟨hR,hQ⟩)

/-- Combine any proved mechanical/sample-sector inclusion with the derived
curve/chord collar. The separate eventual theorem below derives this
mechanical inclusion from the motion/chart and orientation premises. -/
theorem between_cover_of_sector_cover (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (j : Nat) (hsector : ∀ x, MotionSectorCover.sectorDifference a T u j x →
      MotionSectorCover.cover a C T B V u j x)
    (x : Point) (hx : between a T u j x) : cover a C T B P V u g l r chart.positive j x := by
  rcases difference_middle _
    (SectorFan.Region (fun k => (samples u T j k).1) (blocks j) x) _ hx with h | h
  · exact mechanical_cover_inside a C T B P V u g l r chart.positive
      (chart_terminal_nonnegative g l r T parts u chart) d.remainder_nonnegative
      d.time_nonnegative d.position_nonnegative d.velocity_nonnegative j x (hsector x h)
  · have hc : RadialSector.between g (parts j) x := by
      rcases h with ⟨hq,hnc⟩ | ⟨hc,hnq⟩
      · exact Or.inr ⟨(sampled_chord_region g l r T parts u chart j x).mp hq,
          fun h => hnc ((charted_sector g l r T parts u chart x).mpr h)⟩
      · exact Or.inl ⟨(charted_sector g l r T parts u chart x).mp hc,
          fun h => hnq ((sampled_chord_region g l r T parts u chart j x).mpr h)⟩
    exact collar_cover_inside a C T L B P V u d g l r parts chart j x
      (RadialSector.between_subset_collar g (parts j) chart.monotone chart.positive x hc)

theorem eventual_between_cover (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (hdp : ∀ j k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num) :
    ∃ N, ∀ j, N ≤ j → ∀ x, between a T u j x → cover a C T B P V u g l r chart.positive j x := by
  obtain ⟨N,hN⟩ := MotionSectorCover.eventual_sector_difference_cover a C T L B P V u d
    g l r parts chart hdp
  exact ⟨N,fun j hj => between_cover_of_sector_cover a C T L B P V u d g l r parts chart j (hN j hj)⟩

theorem budget_formula (C T B P V : Fraction) (s : Point × Point) (g : Fraction → Fraction)
    (l r : Fraction) (hbase : 0 < (g l).num) (j : Nat) :
    Fraction.equiv (budget C T B P V s g l r hbase j)
      (Fraction.mul (Fraction.mul (Fraction.ofInt 8)
        (Fraction.mul (coefficient C T B P V s g l r hbase) (coefficient C T B P V s g l r hbase)))
        (duration (Fraction.ofInt 1) j)) := by
  apply Fraction.equiv_trans (sum_constant _ _)
  simp only [radius,duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,blocks,
    Int.natCast_pow,Int.ofNat_two,Int.pow_succ,Int.one_mul,Int.mul_one]
  ac_nf
  have ht (z : Int) : 2 * (4 * z) = 8 * z := by omega
  rw [ht]

theorem budgets_vanish (C T B P V : Fraction) (s : Point × Point) (g : Fraction → Fraction)
    (l r : Fraction) (hbase : 0 < (g l).num) (hgr : 0 ≤ (g r).num)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hB : 0 ≤ B.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    Exhaustion.VanishingDifference Fraction.magnitudes (budget C T B P V s g l r hbase) := by
  have hK := coefficient_nonnegative C T B P V s g l r hbase hgr hC hT hB hP hV
  have hv := dyadic_scaled_vanishes
    (Fraction.mul (Fraction.ofInt 8)
      (Fraction.mul (coefficient C T B P V s g l r hbase) (coefficient C T B P V s g l r hbase)))
    (Fraction.ofInt 1)
    (Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hK hK)) (by decide)
  intro eps heps
  obtain ⟨N,hN⟩ := hv eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (budget_formula C T B P V s g l r hbase j)) (hN j hj)⟩

theorem cover_areas (area : TriangleContent.AreaRules) (a : Point → Point) (C T B P V : Fraction)
    (u : Fraction → Point × Point) (g : Fraction → Fraction) (l r : Fraction)
    (hbase : 0 < (g l).num) (hgr : 0 ≤ (g r).num) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num)
    (hB : 0 ≤ B.num) (hP : 0 ≤ P.num) (hV : 0 ≤ V.num) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (cover a C T B P V u g l r hbase j) (A j) ∧ 0 ≤ (A j).num ∧
        Fraction.le (A j) (budget C T B P V (u (Fraction.ofInt 0)) g l r hbase j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A := by
  have hc : ∀ j, ∃ A, area.HasArea (cover a C T B P V u g l r hbase j) A ∧ 0 ≤ A.num ∧
      Fraction.le A (budget C T B P V (u (Fraction.ofInt 0)) g l r hbase j) := by
    intro j
    exact BoxCoverArea.square_cover_area area (MotionSectorCover.centres a T u j)
      (radius C T B P V (u (Fraction.ofInt 0)) g l r hbase j)
      (coefficient_nonnegative C T B P V _ g l r hbase hgr hC hT hB hP hV) (blocks (j+1))
  let A : Nat → Fraction := fun j => Classical.choose (hc j)
  have hA := fun j => Classical.choose_spec (hc j)
  refine ⟨A,hA,?_⟩
  intro eps heps
  obtain ⟨N,hN⟩ := budgets_vanish C T B P V (u (Fraction.ofInt 0)) g l r hbase hgr
    hC hT hB hP hV eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (hA j).2.2 (hN j hj)⟩

/-- Conditional decay of any separately assigned actual between-region
areas. The geometric cover and its vanishing assigned area are derived;
existence of the between-region's own area is not inferred. -/
theorem assigned_between_areas_vanish_of_cover (area : TriangleContent.AreaRules)
    (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (D : Nat → Fraction) (hD : ∀ j, area.HasArea (between a T u j) (D j))
    (hcover : ∃ N, ∀ j, N ≤ j → ∀ x, between a T u j x →
      cover a C T B P V u g l r chart.positive j x) :
    (∀ j, 0 ≤ (D j).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes D := by
  obtain ⟨A,hA,hAv⟩ := cover_areas area a C T B P V u g l r chart.positive
    (chart_terminal_nonnegative g l r T parts u chart) d.remainder_nonnegative
    d.time_nonnegative d.force_nonnegative d.position_nonnegative d.velocity_nonnegative
  obtain ⟨N,hN⟩ := hcover
  refine ⟨fun j => RadialSector.assigned_area_nonnegative area.toSectorRules _ _ (hD j),?_⟩
  intro eps heps
  obtain ⟨M,hM⟩ := hAv eps heps
  refine ⟨max N M,fun j hj => ?_⟩
  have hN' : N ≤ j := Nat.le_trans (Nat.le_max_left N M) hj
  have hM' : M ≤ j := Nat.le_trans (Nat.le_max_right N M) hj
  exact Fraction.magnitudes.lt_of_le_lt
    (area.monotone _ _ _ _ (hN j hN') (hD j) (hA j).1) (hM j hM')

/-- Derive the eventual geometric cover from the finite mechanical
orientation and the existing motion/chart premises, then exhaust any
separately assigned actual between-region areas. -/
theorem assigned_between_areas_vanish (area : TriangleContent.AreaRules)
    (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (hdp : ∀ j k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num)
    (D : Nat → Fraction) (hD : ∀ j, area.HasArea (between a T u j) (D j)) :
    (∀ j, 0 ≤ (D j).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes D :=
  assigned_between_areas_vanish_of_cover area a C T L B P V u d g l r parts chart D hD
    (eventual_between_cover a C T L B P V u d g l r parts chart hdp)

end NewtonLimitDynamics.Polygon.MotionCurveCover
