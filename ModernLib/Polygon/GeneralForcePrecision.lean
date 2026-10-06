import ModernLib.Polygon.ForceClasses
import BarrowLib.Polygon.GeometricTail

/-! A monotone mesh-precision choice extracted from an oracle's force error. -/

namespace NewtonLimitDynamics.Polygon.GeneralForcePrecision

open NewtonLimitDynamics
open ForceClasses

theorem target_positive (E0 : Fraction) (hE : 0 < E0.num) (j : Nat) :
    0 < (GeometricTail.tailCap E0 j).num := hE

noncomputable def threshold (o : Oracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) : Nat :=
  Classical.choose (o.error_vanishes (GeometricTail.tailCap E0 j)
    (target_positive E0 hE j))

theorem threshold_error (o : Oracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j n : Nat)
    (hn : threshold o E0 hE j ≤ n) :
    Fraction.lt (o.error n) (GeometricTail.tailCap E0 j) :=
  Classical.choose_spec (o.error_vanishes (GeometricTail.tailCap E0 j)
    (target_positive E0 hE j)) n hn

noncomputable def precision (o : Oracle) (E0 : Fraction)
    (hE : 0 < E0.num) : Nat → Nat
  | 0 => threshold o E0 hE 0
  | j + 1 => max (precision o E0 hE j) (threshold o E0 hE (j + 1))

theorem precision_successor (o : Oracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) :
    precision o E0 hE j ≤ precision o E0 hE (j + 1) :=
  Nat.le_max_left _ _

theorem precision_monotone (o : Oracle) (E0 : Fraction)
    (hE : 0 < E0.num) {i j : Nat} (hij : i ≤ j) :
    precision o E0 hE i ≤ precision o E0 hE j := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact Nat.le_refl _
  | succ j ih =>
      by_cases he : i = j + 1
      · subst i
        exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (precision_successor o E0 hE j)

theorem precision_threshold (o : Oracle) (E0 : Fraction)
    (hE : 0 < E0.num) :
    (j : Nat) → threshold o E0 hE j ≤ precision o E0 hE j
  | 0 => Nat.le_refl _
  | _ + 1 => Nat.le_max_right _ _

theorem precision_error (o : Oracle) (E0 : Fraction)
    (hE : 0 < E0.num) (j : Nat) :
    Fraction.lt (o.error (precision o E0 hE j))
      (GeometricTail.tailCap E0 j) :=
  threshold_error o E0 hE j _ (precision_threshold o E0 hE j)

end NewtonLimitDynamics.Polygon.GeneralForcePrecision
