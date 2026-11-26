import BarrowLib.Polygon.MotionSectorCover
import BarrowLib.Polygon.UniformRadialSector

/-! Bounded uniformly continuous radial charts of a given rational-time curve
(newtonlean issue 3). The chart keeps every clause of
`MotionSampling.RadialChart` except `monotone` and `positive`: the sample
count, both directions of the curve/graph correspondence and the sample
identification. In their place it carries explicit rational bounds
`m ≤ g ≤ M` with `0 < m` on the slope interval and the rational uniform
modulus `RationalBoundary.UniformOn`. Slope-mesh exhaustion then follows from
the positive-lower-bound width estimate `radial_width_bound_lower`, and the
chord-area errors of an assigned sector area vanish by the cap exhaustion of
`UniformRadialSector`.

Source: the original English statements and checked finite derivations
below. These are project derivations without historical textual attribution
or priority claims; uniform continuity and monotonicity are different
hypotheses, and the monotone API is unchanged. The chart is still supplied:
no theorem here produces a chart for an arbitrary trajectory, and the exact
graph-image clause excludes motions whose rational times miss rational slopes
(research/PROP_I_PATH_DEFECT.md).
-/

namespace NewtonLimitDynamics.Polygon.UniformMotionChart
open NewtonLimitDynamics TimeSubdivision MotionSampling HarmonicDyadic HarmonicTimeComparison

/-- A bounded uniformly continuous radial chart of the full curve image on `[0,T]`
and of its dyadic samples. -/
structure UniformRadialChart (g : Fraction → Fraction) (l r T : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (u : Fraction → Point × Point)
    (m M : Fraction) : Prop where
  lower_positive : 0 < m.num
  bounds : ∀ t, Fraction.le l t → Fraction.le t r → Fraction.le m (g t) ∧ Fraction.le (g t) M
  uniform : RationalBoundary.UniformOn (fun t => (t, g t)) l r
  count : ∀ j, (parts j).count = blocks j
  curve_points : ∀ t, Fraction.le (Fraction.ofInt 0) t → Fraction.le t T →
    ∃ theta, Fraction.le l theta ∧ Fraction.le theta r ∧
      pointEquiv (u t).1 (RadialSector.ray (g theta) theta)
  graph_points : ∀ theta, Fraction.le l theta → Fraction.le theta r →
    ∃ t, Fraction.le (Fraction.ofInt 0) t ∧ Fraction.le t T ∧
      pointEquiv (u t).1 (RadialSector.ray (g theta) theta)
  samples : ∀ j k, k ≤ (parts j).count → pointEquiv (MotionSampling.samples u T j k).1
    (RadialSector.ray (g ((parts j).nodes k)) ((parts j).nodes k))

variable {g : Fraction → Fraction} {l r T m M : Fraction}
  {parts : Nat → MonotoneRectangles.Partition l r} {u : Fraction → Point × Point}

/-- The slope interval of any partition is ordered. -/
theorem ordered (p : MonotoneRectangles.Partition l r) : Fraction.le l r :=
  have hb := MonotoneRectangles.node_bounds p 0 (by omega)
  Fraction.magnitudes.le_trans hb.1 hb.2

/-- The chart identifies the swept sector of the curve with the radial sector of `g`. -/
theorem charted_sector (chart : UniformRadialChart g l r T parts u m M) (x : Point) :
    sweptSector u T x ↔ RadialSector.sector g l r x := by
  constructor
  · rintro ⟨t,ht0,htT,w,hw,he⟩
    obtain ⟨theta,hl,hr,hp⟩ := chart.curve_points t ht0 htT
    exact ⟨theta,hl,hr,w,hw,pointEquiv_trans he (pointScale_congr w hp)⟩
  · rintro ⟨theta,hl,hr,w,hw,he⟩
    obtain ⟨t,ht0,htT,hp⟩ := chart.graph_points theta hl hr
    exact ⟨t,ht0,htT,w,hw,pointEquiv_trans he (pointEquiv_symm (pointScale_congr w hp))⟩

/-- The sampled fan area equals the chord-fan area of the chart's partition. -/
theorem sampled_chord_area (chart : UniformRadialChart g l r T parts u m M) (j : Nat) :
    Fraction.equiv (SectorFan.areaSum (fun k => (samples u T j k).1) (blocks j))
      (RadialSector.chordArea g (parts j)) := by
  rw [← chart.count j]
  apply PolygonFanArea.sum_congr_bounded
  intro k hk
  exact (show Fraction.equiv (Fraction.half _) (Fraction.half _) from by
      apply (Fraction.equiv_iff_toRat _ _).mpr
      simp only [Fraction.toRat_half]
      exact congrArg (fun q : Rat => q / 2) ((Fraction.equiv_iff_toRat _ _).mp (TimeSubdivision.det_congr
    (chart.samples j k (by omega)) (chart.samples j (k+1) (by omega)))))

/-- Slope-mesh exhaustion from the mechanical premises and the positive lower bound
`m`; no monotonicity is used. -/
theorem sampled_mesh (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : UniformRadialChart g l r T parts u m M) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun j => MonotoneRectangles.maxWidth (parts j)) :=
  radial_mesh_vanishes_lower a C T P V g l r parts (samples u T) m chart.lower_positive
    (fun j i hi => (chart.bounds _ (MonotoneRectangles.node_bounds (parts j) i hi).1
      (MonotoneRectangles.node_bounds (parts j) i hi).2).1)
    d.remainder_nonnegative d.time_nonnegative d.position_nonnegative d.velocity_nonnegative
    chart.count d.curve_position_bound d.curve_velocity_bound chart.samples d.local_remainder

/-- Any assigned sector area is approached by the actual chord-fan areas of the chart's
partitions: the cap gap exhaustion is derived from the uniform modulus and the vanishing
mesh, not supplied. -/
theorem chord_errors_vanish (area : SectorFan.AreaRules) (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : UniformRadialChart g l r T parts u m M)
    (A : Fraction) (hA : area.HasArea (RadialSector.sector g l r) A) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun j => (durationDifference A (RadialSector.chordArea g (parts j))).abs) :=
  UniformRadialSector.uniform_chord_errors_vanish area g l r m M (ordered (parts 0))
    chart.lower_positive chart.bounds chart.uniform parts (sampled_mesh a C L B P V d chart) A hA

/-- Any separately assigned areas of the actual curve/chord symmetric differences are
nonnegative and vanish under the subtraction rule. Their existence stays a premise. -/
theorem between_areas_vanish (area : RadialSector.DifferenceAreaRules) (a : Point → Point)
    (C L B P V : Fraction) (d : Conditions a C T L B P V u)
    (chart : UniformRadialChart g l r T parts u m M)
    (D : Nat → Fraction) (hD : ∀ j, area.HasArea (RadialSector.between g (parts j)) (D j)) :
    (∀ j, 0 ≤ (D j).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes D :=
  UniformRadialSector.uniform_between_areas_vanish area g l r m M (ordered (parts 0))
    chart.lower_positive chart.bounds chart.uniform parts (sampled_mesh a C L B P V d chart) D hD

/-- Every monotone positive radial chart whose graph is uniformly continuous is a
uniform chart with bounds `g l ≤ g ≤ g r`, so the new clients extend the old domain. -/
theorem of_radialChart (chart : RadialChart g l r T parts u)
    (huniform : RationalBoundary.UniformOn (fun t => (t, g t)) l r) :
    UniformRadialChart g l r T parts u (g l) (g r) := by
  have hb := MonotoneRectangles.node_bounds (parts 0) 0 (by omega)
  have hlr := Fraction.magnitudes.le_trans hb.1 hb.2
  exact {
    lower_positive := chart.positive
    bounds := fun t hl hr => ⟨chart.monotone l t (Fraction.magnitudes.le_refl _) hl hr,
      chart.monotone t r hl hr (Fraction.magnitudes.le_refl _)⟩
    uniform := huniform
    count := chart.count
    curve_points := chart.curve_points
    graph_points := chart.graph_points
    samples := chart.samples }

/-! Positivity and orientation from the lower bound (issue 3). The positive
half-plane of the samples and of the eventual mechanical polygon, and the
orientation of the sample fan, follow from `m ≤ g` at the chart nodes; no
monotonicity is used. These feed the existing finite fan-difference covers. -/

/-- Every sample has first coordinate at least `m`. -/
theorem sampled_first_lower (chart : UniformRadialChart g l r T parts u m M) (j k : Nat)
    (hk : k ≤ blocks j) : Fraction.le m (samples u T j k).1.1 := by
  have hk' : k ≤ (parts j).count := by rw [chart.count]; exact hk
  have hb := MonotoneRectangles.node_bounds (parts j) k hk'
  exact Fraction.le_equiv_right (chart.bounds _ hb.1 hb.2).1
    (Fraction.equiv_symm (chart.samples j k hk').1)

/-- The mechanical polygon vertices eventually lie in the open right half-plane. -/
theorem polygon_eventually_positive (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : UniformRadialChart g l r T parts u m M) :
    ∃ N, ∀ j, N ≤ j → ∀ k, k ≤ blocks j →
      0 < (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1.1.num := by
  obtain ⟨N,hN⟩ := state_budgets_vanish C T d.remainder_nonnegative d.time_nonnegative
    m chart.lower_positive
  exact ⟨N,fun j hj k hk => positive_first_of_near_lower _ _ m
    (sampled_first_lower chart j k hk)
    (Fraction.magnitudes.lt_of_le_lt (sampled_position_error a C T L B P V u d j k hk) (hN j hj))⟩

/-- The samples lie in the open right half-plane and their fan is positively oriented,
including coincident chart nodes. -/
theorem sampled_positive_oriented (chart : UniformRadialChart g l r T parts u m M) (j : Nat) :
    (∀ k, k ≤ blocks j → 0 < (samples u T j k).1.1.num) ∧
    (∀ k, k < blocks j → 0 ≤ (det (samples u T j k).1 (samples u T j (k+1)).1).num) := by
  have hnode (i : Nat) (hi : i ≤ (parts j).count) : 0 < (g ((parts j).nodes i)).num :=
    RadialSector.positive_of_le _ _ chart.lower_positive
      (chart.bounds _ (MonotoneRectangles.node_bounds (parts j) i hi).1
        (MonotoneRectangles.node_bounds (parts j) i hi).2).1
  refine ⟨fun k hk => RadialSector.positive_of_le _ _ chart.lower_positive
    (sampled_first_lower chart j k hk),?_⟩
  intro k hk
  have hk' : k < (parts j).count := by rw [chart.count]; exact hk
  have he := TimeSubdivision.det_congr (chart.samples j k (by omega)) (chart.samples j (k+1) (by omega))
  exact Fraction.nonnegative_equiv he (RadialSector.ray_orientation _ _ _ _
    (Int.le_of_lt (hnode k (by omega))) (Int.le_of_lt (hnode (k+1) (by omega)))
    ((parts j).ordered k hk'))

/-- The mechanical/sample sector-union symmetric difference is eventually inside the
shrinking sample squares or the terminal connector; only the mechanical fan's
orientation is supplied (historical clients derive it from their own triangle chains). -/
theorem eventual_sampled_sector_difference_cover (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : UniformRadialChart g l r T parts u m M)
    (hdp : ∀ j k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num) :
    ∃ N, ∀ j, N ≤ j → ∀ x,
      ((SectorFan.Region
          (fun k => (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1) (blocks j) x ∧
          ¬ SectorFan.Region (fun k => (samples u T j k).1) (blocks j) x) ∨
        (SectorFan.Region (fun k => (samples u T j k).1) (blocks j) x ∧
          ¬ SectorFan.Region
            (fun k => (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1) (blocks j) x)) →
      ConvexCover.SquareCover (fun k => (samples u T j k).1) (chordRadius C T V j) (blocks j) x ∨
        terminalConnector a T u j x := by
  obtain ⟨N,hN⟩ := polygon_eventually_positive a C L B P V d chart
  refine ⟨N,fun j hj x hx => ?_⟩
  obtain ⟨hq,hdq⟩ := sampled_positive_oriented chart j
  exact sampled_sector_difference_cover a C T L B P V u d j (hN j hj) hq (hdp j) hdq x hx

/-- The mechanical/sample sector difference is eventually inside the existing
`MotionSectorCover` square union. -/
theorem eventual_sector_difference_cover (a : Point → Point) (C L B P V : Fraction)
    (d : Conditions a C T L B P V u) (chart : UniformRadialChart g l r T parts u m M)
    (hdp : ∀ j k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num) :
    ∃ N, ∀ j, N ≤ j → ∀ x, MotionSectorCover.sectorDifference a T u j x →
      MotionSectorCover.cover a C T B V u j x := by
  obtain ⟨N,hN⟩ := eventual_sampled_sector_difference_cover a C L B P V d chart hdp
  refine ⟨N,fun j hj x hx => ?_⟩
  rcases hN j hj x hx with h | h
  · exact MotionSectorCover.edge_cover_inside a C T B V u j d.remainder_nonnegative
      d.time_nonnegative d.force_nonnegative x h
  · exact MotionSectorCover.terminal_cover_inside a C T L B P V u d j x h

end NewtonLimitDynamics.Polygon.UniformMotionChart
