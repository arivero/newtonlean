import BarrowLib.Polygon.TimeSubdivision

/-!
Supporting remainder (STATE.md): the strip-area sum of the constant-force polygon.
For a uniform rational cell `h`, initial velocity `v` and constant accelerative
force `a`, the end-kick recurrence gives velocity `v_n = v + (n·h)·a` and chord
`c_n = h·v_n` (the drift of cell `n`).  The two-cell chord triangle
`(p_n, p_{n+1}, p_{n+2})` has doubled area `det c_n c_{n+1}`.  Because
`det (w + s·a) a = det w a`, every such triangle has the same doubled area
`h³·det(v, a)`, and the signed total over `k` triangles is
`k·h³·det(v, a)`.  The common value can be negative: equality of the triangles
does not equate signed and absolute sums.  An absolute sum would instead be
`k·|h³·det(v, a)|`; its formalization and a geometric strip decomposition remain
open.  Pure finite Fraction arithmetic; no curve, limit or force law.
-/

namespace NewtonLimitDynamics.Polygon.StripArea

open NewtonLimitDynamics
open TimeSubdivision

/-- Velocity after `n` equal end-kick cells. -/
def velAt (h : Fraction) (v a : Point) : Nat → Point
  | 0 => v
  | n + 1 => pointAdd (velAt h v a n) (pointScale h a)

/-- Position at the start of cell `n`, drifting with the incoming velocity. -/
def posAt (h : Fraction) (p v a : Point) : Nat → Point
  | 0 => p
  | n + 1 => pointAdd (posAt h p v a n) (pointScale h (velAt h v a n))

/-- The chord of cell `n`: the drift `h·v_n` of that cell. -/
def chord (h : Fraction) (v a : Point) (n : Nat) : Point := pointScale h (velAt h v a n)

/-- Doubled area of the two-cell chord triangle at cell `n`. -/
def twoCellTwice (h : Fraction) (v a : Point) (n : Nat) : Fraction :=
  det (chord h v a n) (chord h v a (n + 1))

theorem pointSub_add_self_left_equiv (x y : Point) :
    pointEquiv (pointSub (pointAdd x y) x) y :=
  TimeSubdivision.pointSub_add_self_left_equiv x y

/-- The drift of a cell is exactly the position difference `p_{n+1} - p_n`. -/
theorem chord_is_position_diff (h : Fraction) (p v a : Point) (n : Nat) :
    pointEquiv (pointSub (posAt h p v a (n + 1)) (posAt h p v a n)) (chord h v a n) := by
  simp only [posAt, chord]
  exact pointSub_add_self_left_equiv (posAt h p v a n) (pointScale h (velAt h v a n))

/-- The key lemma from the hand computation: `det (w + s·a) a = det w a`. -/
theorem det_kick_direction_constant (s : Fraction) (w a : Point) :
    Fraction.equiv (det (pointAdd w (pointScale s a)) a) (det w a) := by
  have h1 := det_add_left a w (pointScale s a)
  have h2 := det_scale_left s a a
  have h3 := det_self a
  have t1 : Fraction.equiv (det (pointAdd w (pointScale s a)) a)
      (Fraction.add (det w a) (Fraction.mul s (det a a))) :=
    Fraction.equiv_trans h1 (Fraction.add_equiv_left (det w a) h2)
  have t2 : Fraction.equiv (Fraction.mul s (det a a)) (Fraction.mul s (Fraction.ofInt 0)) :=
    Fraction.mul_equiv_left s h3
  have t3 : Fraction.equiv (Fraction.mul s (Fraction.ofInt 0)) (Fraction.ofInt 0) :=
    Fraction.mul_zero s
  have t4 : Fraction.equiv (Fraction.add (det w a) (Fraction.ofInt 0)) (det w a) := by
    simp only [Fraction.add, Fraction.ofInt, Fraction.equiv,
      Int.add_mul, Int.mul_add] <;> ac_nf <;> omega
  exact Fraction.equiv_trans t1
    (Fraction.equiv_trans (Fraction.add_equiv_left (det w a) (Fraction.equiv_trans t2 t3)) t4)

/-- Each velocity has the same determinant with `a` as the initial velocity. -/
theorem vel_det_constant (h : Fraction) (v a : Point) (n : Nat) :
    Fraction.equiv (det (velAt h v a n) a) (det v a) := by
  induction n with
  | zero => exact Fraction.equiv_refl _
  | succ n ih =>
    exact Fraction.equiv_trans (det_kick_direction_constant h (velAt h v a n) a) ih

/-- Every two-cell chord triangle has doubled area `h³·det(v, a)`. -/
theorem two_cell_triangle_constant (h : Fraction) (v a : Point) (n : Nat) :
    Fraction.equiv (twoCellTwice h v a n)
      (Fraction.mul h (Fraction.mul h (Fraction.mul h (det v a)))) := by
  have vn := velAt h v a n
  have vn1 : velAt h v a (n + 1) = pointAdd (velAt h v a n) (pointScale h a) := by simp [velAt]
  simp only [twoCellTwice, chord, vn1]
  -- det (h·v_n) (h·v_{n+1}) = h·det v_n (h·v_{n+1})
  have s1 := det_scale_left h (pointScale h (pointAdd (velAt h v a n) (pointScale h a))) (velAt h v a n)
  -- = h·(h·det v_n v_{n+1})
  have s2 := Fraction.mul_equiv_left h (det_scale_right h (velAt h v a n) (pointAdd (velAt h v a n) (pointScale h a)))
  -- det v_n v_{n+1} = det v_n v_n + h·det v_n a
  have s3 := det_add_right (velAt h v a n) (velAt h v a n) (pointScale h a)
  have s4 := Fraction.add_equiv (det_self (velAt h v a n)) (det_scale_right h (velAt h v a n) a)
  have s5 := Fraction.mul_equiv (Fraction.equiv_refl h) (vel_det_constant h v a n)
  have inner : Fraction.equiv (det (velAt h v a n) (pointAdd (velAt h v a n) (pointScale h a)))
      (Fraction.mul h (det v a)) :=
    Fraction.equiv_trans (Fraction.equiv_trans s3 s4)
      (Fraction.equiv_trans
        (Fraction.add_equiv_left (Fraction.ofInt 0) s5)
        (by simp only [Fraction.add, Fraction.ofInt, Fraction.mul, Fraction.equiv,
            Int.add_mul, Int.mul_add] <;> ac_nf <;> omega))
  have rhs := Fraction.mul_equiv_left h (Fraction.mul_equiv_left h inner)
  exact Fraction.equiv_trans (Fraction.equiv_trans s1 s2) rhs

/-- All two-cell triangles have the same signed doubled area.  No absolute-area
    operation or unsigned sum is asserted. -/
theorem all_triangles_equal (h : Fraction) (v a : Point) (m n : Nat) :
    Fraction.equiv (twoCellTwice h v a m) (twoCellTwice h v a n) :=
  Fraction.equiv_trans (two_cell_triangle_constant h v a m)
    (Fraction.equiv_symm (two_cell_triangle_constant h v a n))

/-- Running sum of the two-cell doubled areas over the first `k` cells. -/
def stripSum (h : Fraction) (v a : Point) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | k + 1 => Fraction.add (stripSum h v a k) (twoCellTwice h v a k)

/-- The signed strip sum over `k` triangles is `k·h³·det(v, a)`. -/
theorem total_strip_area (h : Fraction) (v a : Point) (k : Nat) :
    Fraction.equiv (stripSum h v a k)
      (Fraction.mul (Fraction.ofInt k) (Fraction.mul h (Fraction.mul h (Fraction.mul h (det v a))))) := by
  induction k with
  | zero =>
    simp only [stripSum, Fraction.mul, Fraction.ofInt, Fraction.equiv] <;> omega
  | succ k ih =>
    let H := Fraction.mul h (Fraction.mul h (Fraction.mul h (det v a)))
    simp only [stripSum]
    exact Fraction.equiv_trans
      (Fraction.add_equiv ih (two_cell_triangle_constant h v a k))
      (by simp only [Fraction.mul, Fraction.add, Fraction.ofInt, Fraction.equiv,
          Int.add_mul, Int.mul_add, Int.ofNat_add, Int.mul_one, Int.one_mul] <;>
        ac_nf <;> omega)

end NewtonLimitDynamics.Polygon.StripArea
