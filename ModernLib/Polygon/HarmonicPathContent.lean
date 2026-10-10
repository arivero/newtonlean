import ModernLib.Polygon.HarmonicPathRegion
import ModernLib.Foundation.Polygon.SquareContentValues
import ModernLib.Polygon.PathDefect

/-! Cauchy scalar outer content of the actual constructed harmonic matched
region. The all-cover infimum is represented exactly; the scalar is independent
of the initial covering budget. Ordinary Euclidean area and P5 are separate. -/
namespace NewtonLimitDynamics.Polygon.HarmonicPathContent
open NewtonLimitDynamics
open TimeSubdivision HarmonicDyadic HarmonicTimeRealization CauchyValues PositionValues BinaryTime
open ScalarOrder SquareOuterContent SquareContentValues HarmonicPolygonCurve HarmonicPathRegion

noncomputable def D_meshValue (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) : ScalarValue :=
  contentValue (Region w T s hT hs m) (actualCover w T s hT hs m)

/-- The constructed scalar has precisely the already proved all-cover lower cut. -/
-- Modern dependency score: 232/367 (M=232, H=135; transitive project theorems/axioms).
theorem D_meshValue_lower_cut (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) (q : Fraction) :
    Below q (D_meshValue w T s hT hs m).val ↔ D_mesh w T s hT hs m q :=
  contentValue_lower_cut _ _ q

-- Modern dependency score: 233/368 (M=233, H=135; transitive project theorems/axioms).
theorem D_meshValue_nonnegative (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) :
    Below (Fraction.ofInt 0) (D_meshValue w T s hT hs m).val :=
  contentValue_nonnegative _ _

/-- This is a scalar bound, derived from containment of the actual region. -/
-- Modern dependency score: 234/371 (M=234, H=137; transitive project theorems/axioms).
theorem D_meshValue_budget_bound (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) :
    Within (D_meshValue w T s hT hs m).val (embed (scalarState (Fraction.ofInt 0)))
      (duration (budgetCoefficient w T s) m) :=
  within_mono _ _ _ _ (Fraction.le_of_equiv (actual_budget_geometric w T s hT hs m))
    (contentValue_within_zero _ _)

-- Modern dependency score: 237/375 (M=237, H=138; transitive project theorems/axioms).
theorem D_meshValue_tends_zero (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (eps : Fraction)
    (heps : 0 < eps.num) :
    ∃ N, ∀ m, N ≤ m →
      Within (D_meshValue w T s hT hs m).val (embed (scalarState (Fraction.ofInt 0))) eps := by
  obtain ⟨N,hN⟩ := duration_eventually_small (budgetCoefficient w T s) eps
    (budgetCoefficient_nonnegative w T s hT) heps
  exact ⟨N,fun m hm => within_mono _ _ _ _
    (Fraction.magnitudes.lt_implies_le (hN m hm)) (D_meshValue_budget_bound w T s hT hs m)⟩

/-- The retained instance uses the same geometric-sequence squeeze as the
general construction; it supplies no separate geometric hypothesis. -/
-- Modern dependency score: 247/385 (M=247, H=138; transitive project theorems/axioms).
theorem polygon_trajectory_enclosure (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    PathDefect.PolygonTrajectoryEnclosure
      (fun mesh => D_meshValue w T s hT hs (RationalEnclosure.level mesh))
      (fun mesh => Fraction.mul mesh (budgetCoefficient w T s)) :=
  PathDefect.geometric_sequence_enclosure _ _ (budgetCoefficient_nonnegative w T s hT)
    (D_meshValue_nonnegative w T s hT hs) (D_meshValue_budget_bound w T s hT hs)

-- Modern dependency score: 251/390 (M=251, H=139; transitive project theorems/axioms).
theorem polygon_trajectory_defect_vanishes (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Vanishes (fun mesh => D_meshValue w T s hT hs (RationalEnclosure.level mesh)) :=
  PathDefect.polygon_trajectory_defect_vanishes _ _
    (linear_budget_vanishes _ (budgetCoefficient_nonnegative w T s hT))
    (polygon_trajectory_enclosure w T s hT hs)

-- Modern dependency score: 231/367 (M=231, H=136; transitive project theorems/axioms).
theorem D_meshValue_independent_cover (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat)
    (c : Cover (Region w T s hT hs m)) :
    D_meshValue w T s hT hs m = contentValue (Region w T s hT hs m) c :=
  contentValue_independent_cover _ _ c

-- Modern dependency score: 237/374 (M=237, H=137; transitive project theorems/axioms).
theorem D_meshValue_zero_window (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (m : Nat) (hz : T.num = 0) :
    (D_meshValue w T s hT hs m).val = embed (scalarState (Fraction.ofInt 0)) := by
  apply (within_zero_iff _ _).mp
  apply within_mono _ _ _ _ _ (D_meshValue_budget_bound w T s hT hs m)
  apply Fraction.le_of_equiv
  simp [budgetCoefficient,SquareOuterContent.squareArea,edgeCoefficient,
    HarmonicBinaryPrefix.coefficient,duration,Fraction.equiv,Fraction.add,
    Fraction.mul,Fraction.ofInt,hz]

end NewtonLimitDynamics.Polygon.HarmonicPathContent
