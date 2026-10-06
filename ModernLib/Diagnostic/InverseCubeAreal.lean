/-!
Action diagnostic layer (research/action-arguments/Arg002).  Modern
reconstruction over natural-number magnitudes of two uniform circles compared
by Proposition IV Cor. 1 (force as squared velocity over radius, stated as a
cross-multiplied proportion).  No historical proof uses these theorems.
-/

namespace NewtonLimitDynamics.Diagnostic.InverseCubeAreal

/-- Cor. 1 as a proportion between two circles: `F₁ : F₂ = v₁²/R₁ : v₂²/R₂`. -/
def corOneProportion (F1 F2 R1 R2 v1 v2 : Nat) : Prop :=
  F1 * (v2 * v2) * R1 = F2 * (v1 * v1) * R2

/-- Inverse-cube comparison of the two forces: `F₁R₁³ = F₂R₂³`. -/
def inverseCube (F1 F2 R1 R2 : Nat) : Prop :=
  F1 * (R1 * R1 * R1) = F2 * (R2 * R2 * R2)

/-- Equal squared areal-velocity numerators `(R v)²`. -/
def equalAreal (R1 R2 v1 v2 : Nat) : Prop :=
  (R1 * v1) * (R1 * v1) = (R2 * v2) * (R2 * v2)

/-- Under an inverse-cube comparison, circles related by Cor. 1 have the same
    areal velocity. -/
theorem inverseCube_equalAreal (F1 F2 R1 R2 v1 v2 : Nat) (hF : 0 < F2) (hR : 0 < R2)
    (h1 : corOneProportion F1 F2 R1 R2 v1 v2) (h3 : inverseCube F1 F2 R1 R2) :
    equalAreal R1 R2 v1 v2 := by
  unfold corOneProportion at h1
  unfold inverseCube at h3
  unfold equalAreal
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hF hR)
  calc F2 * R2 * ((R1 * v1) * (R1 * v1))
      = (F2 * (v1 * v1) * R2) * (R1 * R1) := by ac_rfl
    _ = (F1 * (v2 * v2) * R1) * (R1 * R1) := by rw [h1]
    _ = (F1 * (R1 * R1 * R1)) * (v2 * v2) := by ac_rfl
    _ = (F2 * (R2 * R2 * R2)) * (v2 * v2) := by rw [h3]
    _ = F2 * R2 * ((R2 * v2) * (R2 * v2)) := by ac_rfl

/-- Conversely, a common areal velocity with Cor. 1 forces the inverse-cube
    comparison. -/
theorem equalAreal_inverseCube (F1 F2 R1 R2 v1 v2 : Nat) (hv : 0 < v2)
    (h1 : corOneProportion F1 F2 R1 R2 v1 v2) (hA : equalAreal R1 R2 v1 v2) :
    inverseCube F1 F2 R1 R2 := by
  unfold corOneProportion at h1
  unfold equalAreal at hA
  unfold inverseCube
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hv hv)
  calc v2 * v2 * (F1 * (R1 * R1 * R1))
      = (F1 * (v2 * v2) * R1) * (R1 * R1) := by ac_rfl
    _ = (F2 * (v1 * v1) * R2) * (R1 * R1) := by rw [h1]
    _ = F2 * R2 * ((R1 * v1) * (R1 * v1)) := by ac_rfl
    _ = F2 * R2 * ((R2 * v2) * (R2 * v2)) := by rw [hA]
    _ = v2 * v2 * (F2 * (R2 * R2 * R2)) := by ac_rfl

/-- Contrast: under an inverse-square comparison (`F₁R₁² = F₂R₂²`, 1713
    Cor. 6), radii 1 and 4 with speeds 2 and 1 satisfy Cor. 1 but have
    unequal areal velocities 2 and 4. -/
theorem inverseSquare_areal_varies :
    corOneProportion 16 1 1 4 2 1 ∧ 16 * (1 * 1) = 1 * (4 * 4) ∧
      ¬ equalAreal 1 4 2 1 := by
  unfold corOneProportion equalAreal
  decide

end NewtonLimitDynamics.Diagnostic.InverseCubeAreal
