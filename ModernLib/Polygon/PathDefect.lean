import ModernLib.Polygon.RefinementStrip
import ModernLib.Polygon.Enclosure

/-!
Area between paths, separated from Kepler area. The finite construction below
compares coarse edges A_i A_(i+1) with fine pairs A_i B_i A_(i+1). Its signed
closed-boundary area is the difference of the two signed Kepler sums; its
nonnegative patch budget is the sum of absolute triangle areas and retains
lobes of opposite orientation. These are finite paired polygons, not an actual
trajectory. Common spatial endpoints of each patch are built into the data;
matching mechanical data and time intervals are further obligations.

For an actual trajectory gamma and polygon P_mesh over one common time
interval, the main target is the nonnegative area D_mesh between gamma and
P_mesh, including stated endpoint connectors when needed. A valid geometric
patch decomposition/enclosure must identify D_mesh with or bound it by a
nonnegative budget. `PolygonTrajectoryEnclosure` names that supplied premise
explicitly. It is not a definition of D_mesh as a Kepler-sector difference and
does not construct gamma. No integration or curve existence is imported.
-/

namespace NewtonLimitDynamics.Polygon.PathDefect

open NewtonLimitDynamics

def signedGap (coarse inserted : Nat → LatticePoint) (n : Nat) : Int :=
  isum (fun i => refinementStripTwice (coarse i) (inserted i) (coarse (i + 1))) n

def absolutePatchBudget (coarse inserted : Nat → LatticePoint) (n : Nat) : Nat :=
  nsum (fun i => refinementDefect (coarse i) (inserted i) (coarse (i + 1))) n

/-- Signed doubled area swept about S by the coarse polygon; S is the origin. -/
def coarseKeplerTwice (coarse : Nat → LatticePoint) (n : Nat) : Int :=
  isum (fun i => det (coarse i) (coarse (i + 1))) n

def fineKeplerTwice (coarse inserted : Nat → LatticePoint) (n : Nat) : Int :=
  isum (fun i => det (coarse i) (inserted i) + det (inserted i) (coarse (i + 1))) n

/-- Unsigned Kepler triangle sums, counted with multiplicity. -/
def coarseKeplerUnsigned (coarse : Nat → LatticePoint) (n : Nat) : Nat :=
  nsum (fun i => (det (coarse i) (coarse (i + 1))).natAbs) n

def fineKeplerUnsigned (coarse inserted : Nat → LatticePoint) (n : Nat) : Nat :=
  nsum (fun i => (det (coarse i) (inserted i)).natAbs +
    (det (inserted i) (coarse (i + 1))).natAbs) n

/-- Radial closures cancel in the signed difference. This identity says nothing
    about the unsigned area of lobes between the two paths. -/
theorem signed_gap_eq_Kepler_difference (coarse inserted : Nat → LatticePoint) (n : Nat) :
    signedGap coarse inserted n = fineKeplerTwice coarse inserted n -
      coarseKeplerTwice coarse n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [signedGap, fineKeplerTwice, coarseKeplerTwice, isum,
      refinementStripTwice] at *
    omega

/-- The absolute patch budget dominates the absolute signed difference. The
    reverse inequality need not hold because opposite lobes cancel. -/
theorem signed_gap_abs_le_budget (coarse inserted : Nat → LatticePoint) (n : Nat) :
    (signedGap coarse inserted n).natAbs ≤ absolutePatchBudget coarse inserted n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    change (signedGap coarse inserted n +
      refinementStripTwice (coarse n) (inserted n) (coarse (n + 1))).natAbs ≤
      absolutePatchBudget coarse inserted n +
        (refinementStripTwice (coarse n) (inserted n) (coarse (n + 1))).natAbs
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_right ih _)

/-- A uniform local triangle bound controls the entire finite absolute budget. -/
theorem absolute_budget_le_count_mul (coarse inserted : Nat → LatticePoint) (n b : Nat)
    (h : ∀ i, i < n → refinementDefect (coarse i) (inserted i) (coarse (i + 1)) ≤ b) :
    absolutePatchBudget coarse inserted n ≤ n * b := by
  induction n with
  | zero => simp [absolutePatchBudget, nsum]
  | succ n ih =>
    have hold := ih (fun i hi => h i (by omega))
    have hlast := h n (by omega)
    change absolutePatchBudget coarse inserted n +
      refinementDefect (coarse n) (inserted n) (coarse (n + 1)) ≤ (n + 1) * b
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add hold hlast

/-- Moving the origin does not change the area budget between these paths. -/
theorem absolute_budget_translation (origin : LatticePoint)
    (coarse inserted : Nat → LatticePoint) (n : Nat) :
    absolutePatchBudget (fun i => latticeAdd origin (coarse i))
      (fun i => latticeAdd origin (inserted i)) n = absolutePatchBudget coarse inserted n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change absolutePatchBudget (fun i => latticeAdd origin (coarse i))
      (fun i => latticeAdd origin (inserted i)) n +
        (refinementStripTwice (latticeAdd origin (coarse n))
          (latticeAdd origin (inserted n)) (latticeAdd origin (coarse (n + 1)))).natAbs =
      absolutePatchBudget coarse inserted n +
        (refinementStripTwice (coarse n) (inserted n) (coarse (n + 1))).natAbs
    rw [ih, refinementStripTwice_translation]

def exampleCoarse : Nat → LatticePoint := fun i => (i, 3)

def exampleInserted : Nat → LatticePoint := fun i =>
  if i = 0 then (1, 4) else (1, 2)

/-- Both paths have the same signed AND unsigned Kepler sums, but a positive
    area budget between them. Two adjacent, opposite-side triangle lobes have
    doubled unsigned area 1 each; their signed contributions cancel. -/
theorem equal_Kepler_areas_positive_path_defect :
    coarseKeplerTwice exampleCoarse 2 = -6 ∧
      fineKeplerTwice exampleCoarse exampleInserted 2 = -6 ∧
      coarseKeplerUnsigned exampleCoarse 2 = 6 ∧
      fineKeplerUnsigned exampleCoarse exampleInserted 2 = 6 ∧
      signedGap exampleCoarse exampleInserted 2 = 0 ∧
      absolutePatchBudget exampleCoarse exampleInserted 2 = 2 := by
  decide

/-- Explicit geometric premise about the nonnegative area BETWEEN an actual
    trajectory and an impulse polygon over the same interval. The caller must
    supply/construct the trajectory and justify this enclosure. A Kepler area
    or a signed sector-area difference is not an admissible substitution. -/
def PolygonTrajectoryEnclosure {A : Type} [RationalEnclosure.Magnitude A]
    (polygonTrajectoryArea : Fraction → A) (budget : Fraction → Fraction) : Prop :=
  Near Fraction.magnitudes (fun mesh =>
    RationalEnclosure.Magnitude.nonnegative (polygonTrajectoryArea mesh) ∧
      RationalEnclosure.Magnitude.bounded (polygonTrajectoryArea mesh) (budget mesh))

/-- Conditional defect control: a vanishing geometric budget makes the actual
    polygon–trajectory area small. No curve existence or geometric enclosure
    is inferred from the finite Kepler area law. -/
theorem polygon_trajectory_defect_vanishes {A : Type} [RationalEnclosure.Magnitude A]
    (polygonTrajectoryArea : Fraction → A) (budget : Fraction → Fraction)
    (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea := by
  apply enclosed_gap_vanishes polygonTrajectoryArea budget hbudget
  obtain ⟨d, hd, h⟩ := hgeometry
  exact ⟨d, hd, fun mesh hm hmd => (h mesh hm hmd).2⟩

/-- Reindex an actual dyadic geometric magnitude by a positive rational mesh.
The selected family mesh is proved small; the area remains the given value,
and is never defined to be its cover budget. -/
theorem geometric_sequence_enclosure {A : Type} [RationalEnclosure.Magnitude A]
    (area : Nat → A) (C : Fraction) (hC : 0 ≤ C.num)
    (hnonnegative : ∀ m, RationalEnclosure.Magnitude.nonnegative (area m))
    (hbound : ∀ m, RationalEnclosure.Magnitude.bounded (area m) (HarmonicDyadic.duration C m)) :
    PolygonTrajectoryEnclosure (fun mesh => area (RationalEnclosure.level mesh))
      (fun mesh => Fraction.mul mesh C) := by
  refine ⟨Fraction.ofInt 1,(by change (0 : Int) < 1; decide),?_⟩
  intro mesh hm _
  exact ⟨hnonnegative _,RationalEnclosure.Magnitude.bounded_mono _ _ _
    (hbound _) (RationalEnclosure.selected_duration_bound C mesh hC hm)⟩

theorem geometric_sequence_vanishes {A : Type} [RationalEnclosure.Magnitude A]
    (area : Nat → A) (C : Fraction) (hC : 0 ≤ C.num)
    (hnonnegative : ∀ m, RationalEnclosure.Magnitude.nonnegative (area m))
    (hbound : ∀ m, RationalEnclosure.Magnitude.bounded (area m) (HarmonicDyadic.duration C m)) :
    Vanishes (fun mesh => area (RationalEnclosure.level mesh)) :=
  polygon_trajectory_defect_vanishes _ _ (linear_budget_vanishes C hC)
    (geometric_sequence_enclosure area C hC hnonnegative hbound)

end NewtonLimitDynamics.Polygon.PathDefect
