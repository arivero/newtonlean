import BarrowLib.Polygon.MotionSampling
import BarrowLib.Polygon.RadialTriangleCover

/-! Shrinking square covers of the full mechanical/sample-sector difference.
Source: the original English statements and checked finite coordinate
derivations below, without historical textual attribution or priority claim.
The terminal radial triangle is covered by squares along a divided radial
segment. Together with the existing edge-strip squares these form one
finite square union, whose assigned area is constructed under the explicit
existing translation-and-cut convention. No area of the covered difference
or mechanical/curve region B is supplied or inferred from its cover alone.
-/

namespace NewtonLimitDynamics.Polygon.MotionSectorCover
open NewtonLimitDynamics TimeSubdivision PointBounds HarmonicStability
open HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization PolygonFanArea MotionSampling

def joinedCentres (q r : Nat → Point) (n k : Nat) : Point :=
  if k < n then q k else r (k-n)

theorem joined_cover (q r : Nat → Point) (R : Fraction) (n : Nat) (x : Point) :
    ConvexCover.SquareCover (joinedCentres q r n) R (n+n) x ↔
      ConvexCover.SquareCover q R n x ∨ ConvexCover.SquareCover r R n x := by
  constructor
  · rintro ⟨k,hk,hx⟩
    by_cases h : k<n
    · exact Or.inl ⟨k,h,by simpa only [joinedCentres,if_pos h] using hx⟩
    · exact Or.inr ⟨k-n,by omega,by simpa only [joinedCentres,if_neg h] using hx⟩
  · rintro (⟨k,hk,hx⟩ | ⟨k,hk,hx⟩)
    · exact ⟨k,by omega,by simpa only [joinedCentres,if_pos hk] using hx⟩
    · refine ⟨n+k,by omega,?_⟩
      simpa only [joinedCentres,if_neg (by omega : ¬ n+k<n),Nat.add_sub_cancel_left] using hx

theorem square_radius_mono (q x : Point) {R S : Fraction} (h : Fraction.le R S)
    (hx : ConvexCover.SquareContains q R x) : ConvexCover.SquareContains q S x :=
  ⟨Fraction.magnitudes.le_trans hx.1 h,Fraction.magnitudes.le_trans hx.2 h⟩

def centres (a : Point → Point) (T : Fraction) (u : Fraction → Point × Point)
    (j : Nat) : Nat → Point :=
  joinedCentres (fun k => (samples u T j k).1)
    (RadialTriangleCover.centres
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (blocks j)).1 j)
    (blocks j)

def coefficient (C T B V : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (Fraction.mul (chordRadiusCoefficient C T V) T)
    (Fraction.add (Fraction.mul (Fraction.mul (Fraction.ofInt 2) (Fraction.mul C T)) T)
      (BoundedIteration.uniformPositionCap T s B))

def radius (C T B V : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  duration (coefficient C T B V s) j

def cover (a : Point → Point) (C T B V : Fraction) (u : Fraction → Point × Point)
    (j : Nat) : Point → Prop :=
  ConvexCover.SquareCover (centres a T u j)
    (radius C T B V (u (Fraction.ofInt 0)) j) (blocks (j+1))

def budget (C T B V : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  sum (fun _ => Fraction.mul (Fraction.ofInt 4)
    (Fraction.mul (radius C T B V s j) (radius C T B V s j))) (blocks (j+1))

theorem coefficient_nonnegative (C T B V : Fraction) (s : Point × Point)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hB : 0 ≤ B.num) (hV : 0 ≤ V.num) :
    0 ≤ (coefficient C T B V s).num :=
  Fraction.nonnegative_add _ _
    (Fraction.nonnegative_mul _ _ (chordRadiusCoefficient_nonnegative C T V hC hT hV) hT)
    (Fraction.nonnegative_add _ _
      (Fraction.nonnegative_mul _ _
        (Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hC hT)) hT)
      (polygon_position_cap_nonnegative T B s hT hB))

private theorem duration_add (A B : Fraction) (j : Nat) :
    Fraction.equiv (Fraction.add (duration A j) (duration B j))
      (duration (Fraction.add A B) j) := by
  simp only [duration,Fraction.equiv,Fraction.add,Int.add_mul,Int.mul_add]
  ac_nf

private theorem duration_mul (A B : Fraction) (j : Nat) :
    Fraction.equiv (Fraction.mul A (duration B j)) (duration (Fraction.mul A B) j) := by
  simp only [duration,Fraction.equiv,Fraction.mul]
  ac_nf

theorem radius_parts (C T B V : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv
      (Fraction.add (chordRadius C T V j)
        (Fraction.add (stateBudget C T j) (duration (BoundedIteration.uniformPositionCap T s B) j)))
      (radius C T B V s j) := by
  apply Fraction.equiv_trans (Fraction.add_equiv (duration_mul _ _ j)
    (Fraction.add_equiv (duration_mul _ _ j) (Fraction.equiv_refl _)))
  exact Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _) (duration_add _ _ j))
    (duration_add _ _ j)

theorem chord_radius_le (C T B V : Fraction) (s : Point × Point) (j : Nat)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hB : 0 ≤ B.num) :
    Fraction.le (chordRadius C T V j) (radius C T B V s j) := by
  have hE : 0 ≤ (stateBudget C T j).num := stateBudget_nonnegative C T j hC hT
  have hR : 0 ≤ (duration (BoundedIteration.uniformPositionCap T s B) j).num :=
    polygon_position_cap_nonnegative T B s hT hB
  exact Fraction.le_equiv_right
    (Fraction.le_add_nonnegative _ _ (Fraction.nonnegative_add _ _ hE hR))
    (radius_parts C T B V s j)

theorem terminal_radius_le (C T B V : Fraction) (s : Point × Point) (j : Nat)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hV : 0 ≤ V.num) :
    Fraction.le
      (Fraction.add (stateBudget C T j) (duration (BoundedIteration.uniformPositionCap T s B) j))
      (radius C T B V s j) := by
  have hK := chordRadiusCoefficient_nonnegative C T V hC hT hV
  have hchord : 0 ≤ (chordRadius C T V j).num := Fraction.nonnegative_mul _ _ hK hT
  exact Fraction.le_equiv_right (Fraction.le_equiv_right
    (Fraction.le_add_nonnegative _ _ hchord) (Fraction.add_comm _ _))
    (radius_parts C T B V s j)

/-- Two groups of 2^j squares, each of radius K/2^j, have summed budget
8*K^2/2^j. No disjointness is used. -/
theorem budget_formula (C T B V : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv (budget C T B V s j)
      (Fraction.mul (Fraction.mul (Fraction.ofInt 8)
        (Fraction.mul (coefficient C T B V s) (coefficient C T B V s)))
        (duration (Fraction.ofInt 1) j)) := by
  apply Fraction.equiv_trans (sum_constant _ _)
  simp only [radius,duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,blocks,
    Int.natCast_pow,Int.ofNat_two,Int.pow_succ,Int.one_mul,Int.mul_one]
  ac_nf
  have ht (z : Int) : 2 * (4 * z) = 8 * z := by omega
  rw [ht]

theorem budgets_vanish (C T B V : Fraction) (s : Point × Point)
    (hC : 0 ≤ C.num) (hT : 0 ≤ T.num) (hB : 0 ≤ B.num) (hV : 0 ≤ V.num) :
    Exhaustion.VanishingDifference Fraction.magnitudes (budget C T B V s) := by
  have hK := coefficient_nonnegative C T B V s hC hT hB hV
  have hv := dyadic_scaled_vanishes
    (Fraction.mul (Fraction.ofInt 8) (Fraction.mul (coefficient C T B V s) (coefficient C T B V s)))
    (Fraction.ofInt 1)
    (Fraction.nonnegative_mul _ _ (by decide) (Fraction.nonnegative_mul _ _ hK hK)) (by decide)
  intro eps heps
  obtain ⟨N,hN⟩ := hv eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (budget_formula C T B V s j)) (hN j hj)⟩

/-- The full square cover has a constructed nonnegative assigned area
bounded by its vanishing budget. The area convention remains explicit. -/
theorem cover_areas (area : TriangleContent.AreaRules) (a : Point → Point) (C T B V : Fraction)
    (u : Fraction → Point × Point) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num)
    (hB : 0 ≤ B.num) (hV : 0 ≤ V.num) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (cover a C T B V u j) (A j) ∧ 0 ≤ (A j).num ∧
        Fraction.le (A j) (budget C T B V (u (Fraction.ofInt 0)) j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A := by
  have hc : ∀ j, ∃ A, area.HasArea (cover a C T B V u j) A ∧ 0 ≤ A.num ∧
      Fraction.le A (budget C T B V (u (Fraction.ofInt 0)) j) := by
    intro j
    exact BoxCoverArea.square_cover_area area (centres a T u j)
      (radius C T B V (u (Fraction.ofInt 0)) j)
      (coefficient_nonnegative C T B V _ hC hT hB hV) (blocks (j+1))
  let A : Nat → Fraction := fun j => Classical.choose (hc j)
  have hA := fun j => Classical.choose_spec (hc j)
  refine ⟨A,hA,?_⟩
  intro eps heps
  obtain ⟨N,hN⟩ := budgets_vanish C T B V (u (Fraction.ofInt 0)) hC hT hB hV eps heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (hA j).2.2 (hN j hj)⟩

theorem edge_cover_inside (a : Point → Point) (C T B V : Fraction)
    (u : Fraction → Point × Point) (j : Nat) (hC : 0 ≤ C.num) (hT : 0 ≤ T.num)
    (hB : 0 ≤ B.num) (x : Point)
    (hx : ConvexCover.SquareCover (fun k => (samples u T j k).1)
      (chordRadius C T V j) (blocks j) x) : cover a C T B V u j x := by
  obtain ⟨k,hk,hx⟩ := hx
  change ConvexCover.SquareCover (joinedCentres _ _ (blocks j)) _ (blocks (j+1)) x
  rw [blocks_succ,joined_cover]
  exact Or.inl ⟨k,hk,square_radius_mono _ x (chord_radius_le C T B V _ j hC hT hB) hx⟩

/-- The terminal triangle is enclosed by the second group of squares,
using the derived mechanical cap and terminal sample error. -/
theorem terminal_cover_inside (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (j : Nat) (x : Point) (hx : terminalConnector a T u j x) :
    cover a C T B V u j x := by
  let p := (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (blocks j)).1
  let q := (samples u T j (blocks j)).1
  let R := BoundedIteration.uniformPositionCap T (u (Fraction.ofInt 0)) B
  have hR := polygon_position_cap_nonnegative T B (u (Fraction.ofInt 0))
    d.time_nonnegative d.force_nonnegative
  have hp := polygon_position_bound a C T L B P V u d j (blocks j) (Nat.le_refl _)
  have hq : Fraction.le (pointNorm (pointSub q p)) (stateBudget C T j) :=
    Fraction.le_equiv_left (FiniteEstimates.pointDistance_symm q p)
      (sampled_position_error a C T L B P V u d j (blocks j) (Nat.le_refl _))
  obtain ⟨k,hk,hx⟩ := RadialTriangleCover.terminal_triangle_square_cover p q x R
    (stateBudget C T j) hR
    (stateBudget_nonnegative C T j d.remainder_nonnegative d.time_nonnegative) hp hq j hx
  change ConvexCover.SquareCover (joinedCentres _ _ (blocks j)) _ (blocks (j+1)) x
  rw [blocks_succ,joined_cover]
  exact Or.inr ⟨k,hk,square_radius_mono _ x
    (terminal_radius_le C T B V _ j d.remainder_nonnegative d.time_nonnegative d.velocity_nonnegative) hx⟩

def sectorDifference (a : Point → Point) (T : Fraction)
    (u : Fraction → Point × Point) (j : Nat) (x : Point) : Prop :=
  (SectorFan.Region
      (fun k => (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1) (blocks j) x ∧
    ¬ SectorFan.Region (fun k => (samples u T j k).1) (blocks j) x) ∨
  (SectorFan.Region (fun k => (samples u T j k).1) (blocks j) x ∧
    ¬ SectorFan.Region
      (fun k => (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1) (blocks j) x)

/-- A full finite cover of the actual sector-union symmetric difference.
The positive half-plane and orientation premises are exactly those of the
existing finite fan inclusion. No inclusion or area is supplied. -/
theorem sector_difference_cover (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u) (j : Nat)
    (hp : ∀ k, k ≤ blocks j →
      0 < (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1.1.num)
    (hq : ∀ k, k ≤ blocks j → 0 < (samples u T j k).1.1.num)
    (hdp : ∀ k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num)
    (hdq : ∀ k, k < blocks j → 0 ≤ (det (samples u T j k).1 (samples u T j (k+1)).1).num)
    (x : Point) (hx : sectorDifference a T u j x) : cover a C T B V u j x := by
  rcases sampled_sector_difference_cover a C T L B P V u d j hp hq hdp hdq x hx with h | h
  · exact edge_cover_inside a C T B V u j d.remainder_nonnegative d.time_nonnegative
      d.force_nonnegative x h
  · exact terminal_cover_inside a C T L B P V u d j x h

/-- The full chart and motion estimates derive the half-plane and sample
orientation eventually. Historical clients separately derive mechanical
orientation from their own finite triangle chains. -/
theorem eventual_sector_difference_cover (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (hdp : ∀ j k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num) :
    ∃ N, ∀ j, N ≤ j → ∀ x, sectorDifference a T u j x → cover a C T B V u j x := by
  obtain ⟨N,hN⟩ := eventual_sampled_sector_difference_cover a C T L B P V u d
    g l r parts chart hdp
  refine ⟨N,fun j hj x hx => ?_⟩
  rcases hN j hj x hx with h | h
  · exact edge_cover_inside a C T B V u j d.remainder_nonnegative d.time_nonnegative
      d.force_nonnegative x h
  · exact terminal_cover_inside a C T L B P V u d j x h

/-- The actual sector difference is eventually inside a finite square
union with constructed nonnegative assigned area and vanishing budget.
The chart and mechanical orientation are explicit premises, and neither
an enclosing inclusion nor an area of the difference is supplied. -/
theorem eventual_cover_areas (area : TriangleContent.AreaRules)
    (a : Point → Point) (C T L B P V : Fraction)
    (u : Fraction → Point × Point) (d : Conditions a C T L B P V u)
    (g : Fraction → Fraction) (l r : Fraction)
    (parts : Nat → MonotoneRectangles.Partition l r) (chart : RadialChart g l r T parts u)
    (hdp : ∀ j k, k < blocks j → 0 ≤ (det
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) k).1
      (BoundedIteration.run a (duration T j) (u (Fraction.ofInt 0)) (k+1)).1).num) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (cover a C T B V u j) (A j) ∧ 0 ≤ (A j).num ∧
        Fraction.le (A j) (budget C T B V (u (Fraction.ofInt 0)) j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A ∧
      ∃ N, ∀ j, N ≤ j → ∀ x, sectorDifference a T u j x → cover a C T B V u j x := by
  obtain ⟨A,hA,hvanish⟩ := cover_areas area a C T B V u d.remainder_nonnegative
    d.time_nonnegative d.force_nonnegative d.velocity_nonnegative
  exact ⟨A,hA,hvanish,eventual_sector_difference_cover a C T L B P V u d g l r parts chart hdp⟩

/-- Any separately assigned sector-difference area is nonnegative and at
most the constructed full-cover budget. This does not construct that
sector-difference area. -/
theorem assigned_difference_bound (area : TriangleContent.AreaRules)
    (a : Point → Point) (C T L B P V : Fraction) (u : Fraction → Point × Point)
    (d : Conditions a C T L B P V u) (j : Nat)
    (hcover : ∀ x, sectorDifference a T u j x → cover a C T B V u j x)
    (D : Fraction) (hD : area.HasArea (sectorDifference a T u j) D) :
    0 ≤ D.num ∧ Fraction.le D (budget C T B V (u (Fraction.ofInt 0)) j) := by
  obtain ⟨A,hA,_⟩ := cover_areas area a C T B V u d.remainder_nonnegative
    d.time_nonnegative d.force_nonnegative d.velocity_nonnegative
  exact ⟨RadialSector.assigned_area_nonnegative area.toSectorRules _ _ hD,
    Fraction.magnitudes.le_trans
      (area.monotone _ _ _ _ hcover hD (hA j).1) (hA j).2.2⟩

end NewtonLimitDynamics.Polygon.MotionSectorCover
