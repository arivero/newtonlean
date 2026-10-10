/-!
Finite rational tolerances for multiplication by a nonnegative coefficient.
Source: the exact English statement and checked derivation below. This records
proof provenance for this formulation, without historical attribution or
mathematical priority. Core Rat arithmetic is encoding infrastructure.
-/
namespace NewtonLimitDynamics.Polygon.HarmonicTimeRealization

def factorDelta (C eps : Rat) (_hC : 0 ≤ C) : Rat := eps / (C + 1)

/-- The chosen tolerance controls multiplication by the coefficient. -/
theorem factor_delta_weak (C eps : Rat) (hC : 0 ≤ C) (heps : 0 ≤ eps) :
    factorDelta C eps hC * C ≤ eps := by
  have hn : 0 ≤ factorDelta C eps hC := by
    grind [factorDelta, Rat.div_def, Rat.inv_pos, Rat.mul_nonneg]
  have heq : factorDelta C eps hC * (C + 1) = eps := by
    unfold factorDelta
    rw [Rat.div_mul_cancel (by grind)]
  grind [Rat.mul_nonneg]

end NewtonLimitDynamics.Polygon.HarmonicTimeRealization
