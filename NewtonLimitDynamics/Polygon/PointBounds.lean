import NewtonLimitDynamics.Polygon.TimeSubdivision

/-!
Coordinate L1 magnitudes for finite rational polygon data. These diagnostics
depend on the chosen coordinates; they are neither Euclidean area nor a
physical position/velocity norm without a calibration of their units.
-/

namespace NewtonLimitDynamics.Polygon.PointBounds

open NewtonLimitDynamics
open TimeSubdivision

def pointNorm (p : Point) : Fraction := Fraction.add p.1.abs p.2.abs
def stateNorm (s : Point × Point) : Fraction :=
  Fraction.add (pointNorm s.1) (pointNorm s.2)

def stateEquiv (s t : Point × Point) : Prop :=
  pointEquiv s.1 t.1 ∧ pointEquiv s.2 t.2

private theorem add_equiv {a b c d : Fraction} (h : Fraction.equiv a b)
    (k : Fraction.equiv c d) :
    Fraction.equiv (Fraction.add a c) (Fraction.add b d) :=
  Fraction.equiv_trans (Fraction.add_equiv_right c h)
    (Fraction.equiv_trans (Fraction.add_comm b c)
      (Fraction.equiv_trans (Fraction.add_equiv_right b k) (Fraction.add_comm d b)))

theorem pointNorm_nonnegative (p : Point) : 0 ≤ (pointNorm p).num := by
  unfold pointNorm Fraction.add
  exact Int.add_nonneg
    (Int.mul_nonneg (Fraction.abs_num_nonnegative _) (Int.le_of_lt p.2.abs.den_pos))
    (Int.mul_nonneg (Fraction.abs_num_nonnegative _) (Int.le_of_lt p.1.abs.den_pos))

theorem stateNorm_nonnegative (s : Point × Point) : 0 ≤ (stateNorm s).num := by
  unfold stateNorm Fraction.add
  exact Int.add_nonneg
    (Int.mul_nonneg (pointNorm_nonnegative _) (Int.le_of_lt (pointNorm s.2).den_pos))
    (Int.mul_nonneg (pointNorm_nonnegative _) (Int.le_of_lt (pointNorm s.1).den_pos))

theorem pointNorm_equiv {p q : Point} (h : pointEquiv p q) :
    Fraction.equiv (pointNorm p) (pointNorm q) :=
  add_equiv (Fraction.abs_equiv h.1) (Fraction.abs_equiv h.2)

theorem stateNorm_equiv {s t : Point × Point} (h : stateEquiv s t) :
    Fraction.equiv (stateNorm s) (stateNorm t) :=
  add_equiv (pointNorm_equiv h.1) (pointNorm_equiv h.2)

theorem pointNorm_add_le (p q : Point) :
    Fraction.le (pointNorm (pointAdd p q))
      (Fraction.add (pointNorm p) (pointNorm q)) := by
  have h := Fraction.add_le_add (Fraction.abs_add_le p.1 q.1)
    (Fraction.abs_add_le p.2 q.2)
  apply Fraction.le_equiv_right h
  simp only [Fraction.equiv, Fraction.add, pointNorm]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

theorem pointNorm_scale (d : Fraction) (p : Point) :
    Fraction.equiv (pointNorm (pointScale d p)) (Fraction.mul d.abs (pointNorm p)) := by
  simp only [Fraction.equiv, pointNorm, pointScale, Fraction.abs, Fraction.add,
    Fraction.mul, Int.natAbs_mul, Int.ofNat_mul]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

theorem stateNorm_add_le (s t : Point × Point) :
    Fraction.le (stateNorm (pointAdd s.1 t.1, pointAdd s.2 t.2))
      (Fraction.add (stateNorm s) (stateNorm t)) := by
  have h := Fraction.add_le_add (pointNorm_add_le s.1 t.1)
    (pointNorm_add_le s.2 t.2)
  apply Fraction.le_equiv_right h
  simp only [Fraction.equiv, Fraction.add, stateNorm]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

theorem stateNorm_scale (d : Fraction) (s : Point × Point) :
    Fraction.equiv
      (stateNorm (pointScale d s.1, pointScale d s.2))
      (Fraction.mul d.abs (stateNorm s)) := by
  simp only [Fraction.equiv, stateNorm, pointNorm, pointScale, Fraction.abs,
    Fraction.add, Fraction.mul, Int.natAbs_mul, Int.ofNat_mul]
  simp only [Int.add_mul, Int.mul_add]
  ac_nf

end NewtonLimitDynamics.Polygon.PointBounds
