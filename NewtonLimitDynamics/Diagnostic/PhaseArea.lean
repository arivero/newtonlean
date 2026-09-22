import NewtonLimitDynamics.Polygon.TimeSubdivision

/-!
Action diagnostic layer (research/action-arguments Arg004).  One-dimensional
phase plane `(q, v)` for the cell of Proposition I's finite construction:
inertial drift (Law I), then the impulse of the force at the arrival point
(Law II, laws' Corollary I).  The construction is the same in De Motu
(NATP00089 par9, NATP00090 par17), 1687 (NATP00077 par45) and 1713
(NATP00082 par51).  Modern rational reconstruction; no limit is taken.

Each step moves one coordinate by an amount depending only on the other
(a shear), so each line of fixed velocity (drift) or fixed position (impulse)
is translated rigidly: Cavalieri's comparison of equal chords.  For affine
fields (constant force; force as distance) the doubled signed area of every
phase triangle is preserved exactly, at every cell duration.  The exact
energy-type invariant of the constant-force cell depends on the duration.
-/

namespace NewtonLimitDynamics.Diagnostic.PhaseArea

open NewtonLimitDynamics
open NewtonLimitDynamics.Polygon.TimeSubdivision

/-- A phase point `(position, velocity)`. -/
abbrev Phase := Point

def negF (w : Fraction) : Fraction := ⟨-w.num, w.den, w.den_pos⟩
def fsub (a b : Fraction) : Fraction := Fraction.add a (negF b)

/-- Law I drift for duration `d`. -/
def drift (d : Fraction) (z : Phase) : Phase := (Fraction.add z.1 (Fraction.mul d z.2), z.2)

/-- Impulse of an arbitrary field `F` at the current position. -/
def kick (F : Fraction → Fraction) (d : Fraction) (z : Phase) : Phase :=
  (z.1, Fraction.add z.2 (Fraction.mul d (F z.1)))

/-- One cell of the construction: drift, then the impulse at the arrival point. -/
def cell (F : Fraction → Fraction) (d : Fraction) (z : Phase) : Phase := kick F d (drift d z)

/-- `n` equal cells. -/
def cells (F : Fraction → Fraction) (d : Fraction) : Nat → Phase → Phase
  | 0, z => z
  | n + 1, z => cells F d n (cell F d z)

/-- Doubled signed area of a phase triangle. -/
def area2 (z0 z1 z2 : Phase) : Fraction := det (pointSub z1 z0) (pointSub z2 z0)

/-- Cavalieri, drift: two phase points with the same velocity keep their
    position difference.  Holds for every field. -/
theorem drift_rigid (d q q' v : Fraction) :
    Fraction.equiv (fsub (drift d (q', v)).1 (drift d (q, v)).1) (fsub q' q) := by
  unfold fsub negF drift Fraction.equiv Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- Cavalieri, impulse: two phase points at the same position keep their
    velocity difference, for an arbitrary field `F`. -/
theorem kick_rigid (F : Fraction → Fraction) (d q v v' : Fraction) :
    Fraction.equiv (fsub (kick F d (q, v')).2 (kick F d (q, v)).2) (fsub v' v) := by
  unfold fsub negF kick Fraction.equiv Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- The affine field `F(q) = c - w*q`: constant force (`w = 0`) or force as
    distance toward the origin (`w > 0`). -/
def affine (c w : Fraction) : Fraction → Fraction :=
  fun q => Fraction.add c (Fraction.mul (negF w) q)

theorem drift_area2 (d : Fraction) (z0 z1 z2 : Phase) :
    Fraction.equiv (area2 (drift d z0) (drift d z1) (drift d z2)) (area2 z0 z1 z2) := by
  unfold area2 det pointSub pointNeg pointAdd drift Fraction.equiv Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

theorem kick_area2 (c w d : Fraction) (z0 z1 z2 : Phase) :
    Fraction.equiv (area2 (kick (affine c w) d z0) (kick (affine c w) d z1) (kick (affine c w) d z2))
      (area2 z0 z1 z2) := by
  unfold area2 det pointSub pointNeg pointAdd kick affine negF Fraction.equiv Fraction.add
    Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- One cell preserves the doubled phase area of every triangle, for every
    duration. -/
theorem cell_area2 (c w d : Fraction) (z0 z1 z2 : Phase) :
    Fraction.equiv
      (area2 (cell (affine c w) d z0) (cell (affine c w) d z1) (cell (affine c w) d z2))
      (area2 z0 z1 z2) :=
  Fraction.equiv_trans (kick_area2 c w d _ _ _) (drift_area2 d z0 z1 z2)

/-- Every equal-cell schedule, at every mesh, preserves it. -/
theorem cells_area2 (c w d : Fraction) :
    (n : Nat) → (z0 z1 z2 : Phase) →
    Fraction.equiv
      (area2 (cells (affine c w) d n z0) (cells (affine c w) d n z1) (cells (affine c w) d n z2))
      (area2 z0 z1 z2)
  | 0, _, _, _ => Fraction.equiv_refl _
  | n + 1, z0, z1, z2 =>
      Fraction.equiv_trans (cells_area2 c w d n _ _ _) (cell_area2 c w d z0 z1 z2)

/-- The exact energy-type invariant of the constant-force cell,
    `v² - 2*a*q - d*a*v`, involves the cell duration `d`. -/
def energyD (a d : Fraction) (z : Phase) : Fraction :=
  fsub (fsub (Fraction.mul z.2 z.2) (Fraction.add (Fraction.mul a z.1) (Fraction.mul a z.1)))
    (Fraction.mul d (Fraction.mul a z.2))

theorem cell_energyD (a d : Fraction) (z : Phase) :
    Fraction.equiv (energyD a d (cell (fun _ => a) d z)) (energyD a d z) := by
  unfold energyD fsub negF cell kick drift Fraction.equiv Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

def one : Fraction := Fraction.ofInt 1
def zero : Fraction := Fraction.ofInt 0
def half : Fraction := ⟨1, 2, by decide⟩

/-- The duration-dependent invariant differs between meshes at the same state
    (`a = 1`, state `(0, 1)`): `0` for `d = 1`, `1/2` for `d = 1/2`. -/
theorem energyD_depends_on_mesh :
    ¬ Fraction.equiv (energyD one one (zero, one)) (energyD one half (zero, one)) := by
  decide

/-- Refinement example, force as distance (`c = 0`, `w = 1`): one cell of
    duration 1 and two cells of duration 1/2 send the phase point `(1, 0)` to
    different places, while both keep the unit triangle's doubled area 1. -/
theorem refinement_moves_points_keeps_area :
    ¬ pointEquiv (cells (affine zero one) one 1 (one, zero))
        (cells (affine zero one) half 2 (one, zero)) ∧
    Fraction.equiv
      (area2 (cells (affine zero one) one 1 (zero, zero)) (cells (affine zero one) one 1 (one, zero))
        (cells (affine zero one) one 1 (zero, one))) one ∧
    Fraction.equiv
      (area2 (cells (affine zero one) half 2 (zero, zero)) (cells (affine zero one) half 2 (one, zero))
        (cells (affine zero one) half 2 (zero, one))) one := by
  decide

end NewtonLimitDynamics.Diagnostic.PhaseArea
