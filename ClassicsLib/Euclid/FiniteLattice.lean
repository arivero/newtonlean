import BarrowLib.Polygon.Finite
import ClassicsLib.Euclid.PropositionI37
import ClassicsLib.Euclid.PropositionI38

namespace NewtonLimitDynamics.Polygon

def lattice : EuclideanConstruction LatticePoint Int :=
  ⟨det, extend, kick, extension_identity, parallel_identity⟩

/-- Checked orientation control: signed and unsigned sums agree here. -/
theorem positive_orientation_unsigned_example :
    swept lattice (1, 0) (1, 1) (fun _ => 0) 3 = 3 ∧
      unsignedBlock lattice (1, 0) (1, 1) (fun _ => 0) 0 3 = 3 := by
  decide

/-- Reversing orientation preserves unsigned magnitude, not the signed sum. -/
theorem negative_orientation_unsigned_example :
    swept lattice (1, 0) (1, -1) (fun _ => 0) 3 = -3 ∧
      unsignedBlock lattice (1, 0) (1, -1) (fun _ => 0) 0 3 = 3 ∧
      swept lattice (1, 0) (1, -1) (fun _ => 0) 3 ≠
        (unsignedBlock lattice (1, 0) (1, -1) (fun _ => 0) 0 3 : Int) := by
  decide

/-- Radial degeneracy, rest, and empty blocks need no area division. -/
theorem degenerate_unsigned_examples :
    unsignedBlock lattice (1, 0) (2, 0) (fun _ => -1) 2 3 = 0 ∧
      unsignedBlock lattice (1, 0) (1, 0) (fun _ => 0) 2 3 = 0 ∧
      unsignedBlock lattice (1, 0) (1, 1) (fun _ => 0) 4 0 = 0 := by
  decide

/-- Even inward radial impulses can revisit triangles. The unsigned cell sum
    counts repeated coverage and therefore cannot identify a sector union. -/
theorem repeated_triangle_coverage_example :
    motion lattice (1, 0) (0, 1) (fun _ => -2) 4 = ((1, 0), (0, 1)) ∧
      unsignedBlock lattice (1, 0) (0, 1) (fun _ => -2) 0 4 = 4 ∧
      unsignedBlock lattice (1, 0) (0, 1) (fun _ => -2) 0 8 = 8 := by
  decide

/-- Zero force is permitted; radial/zero-area configurations need no division. -/
example : swept lattice (1,0) (1,1) (fun _ => 0) 3 = 3 := by decide
example : swept lattice (1,0) (2,0) (fun _ => -1) 3 = 0 := by decide

end NewtonLimitDynamics.Polygon
