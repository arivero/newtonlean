import NewtonLimitDynamics.Polygon.CentralSchedule

/-!
Stability of the finite impulse construction for the linear central field
`a(p) = -w*p` (force proportional to distance; compare Proposition IV Cor. 3,
equal periods with forces as radii, 1687 NATP00077 par64, 1713 NATP00082 par75).
With equal cells `d`, the construction conserves exactly the quadratic form
`w|x|² + w*d*(x·v) + |v|²`, which equals `w|x + (d/2)v|² + (1 - w*d²/4)|v|²`
(stated with `d = c + c` to avoid numeric literals).
For `w > 0` and `w*d² < 4` this bounds every refined orbit.  Modern rational
reconstruction; no ODE theorem, limit or curve is used or produced.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicStability

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule

def negF (w : Fraction) : Fraction := ⟨-w.num, w.den, w.den_pos⟩

/-- The central field `a(p) = -w*p`. -/
def linearField (w : Fraction) : Field := fun p => pointScale (negF w) p

def dot (p q : Point) : Fraction :=
  Fraction.add (Fraction.mul p.1 q.1) (Fraction.mul p.2 q.2)

/-- The discrete invariant of the equal-cell construction. -/
def invariant (w d : Fraction) (s : Point × Point) : Fraction :=
  Fraction.add (Fraction.add (Fraction.mul w (dot s.1 s.1))
    (Fraction.mul (Fraction.mul w d) (dot s.1 s.2))) (dot s.2 s.2)

theorem linearField_central (w : Fraction) : central (linearField w) := by
  intro p
  unfold linearField negF pointScale det Fraction.equiv Fraction.add Fraction.mul Fraction.ofInt
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.mul_one, Int.zero_mul]
  ac_nf
  omega

/-- One cell of duration `d` conserves the invariant built with the same `d`. -/
theorem cell_invariant (w d : Fraction) (s : Point × Point) :
    Fraction.equiv (invariant w d (cell (linearField w) d s)) (invariant w d s) := by
  unfold invariant dot cell linearField negF pointAdd pointScale Fraction.equiv Fraction.add
    Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- Every equal-cell schedule conserves it. -/
theorem schedule_invariant (w d : Fraction) :
    (n : Nat) → (s : Point × Point) →
    Fraction.equiv (invariant w d (schedule (linearField w) (List.replicate n d) s))
      (invariant w d s)
  | 0, _ => Fraction.equiv_refl _
  | n + 1, s =>
      Fraction.equiv_trans (schedule_invariant w d n (cell (linearField w) d s))
        (cell_invariant w d s)

/-- `1 - w*c²`, the stability margin for cells of duration `d = 2c`. -/
def margin (w c : Fraction) : Fraction :=
  Fraction.add (Fraction.ofInt 1) (negF (Fraction.mul w (Fraction.mul c c)))

/-- Completed square, for cells of duration `d = c + c`: the invariant equals
    `w|x + c*v|² + (1 - w*c²)|v|²`.  When `w ≥ 0` and `w*c² < 1` (that is,
    `w*d² < 4`) both coefficients are nonnegative, so every equal-cell orbit
    keeps `|v|²` and `w|x + c*v|²` bounded by its initial invariant
    (`schedule_speed_bound`, `schedule_position_bound`). -/
theorem invariant_square (w c : Fraction) (s : Point × Point) :
    Fraction.equiv (invariant w (Fraction.add c c) s)
      (Fraction.add
        (Fraction.mul w (dot (pointAdd s.1 (pointScale c s.2)) (pointAdd s.1 (pointScale c s.2))))
        (Fraction.mul (margin w c) (dot s.2 s.2))) := by
  unfold invariant margin dot negF pointAdd pointScale Fraction.equiv Fraction.add Fraction.mul
    Fraction.ofInt
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.mul_one, Int.one_mul]
  ac_nf
  omega

private theorem self_mul_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := by omega
    have k := Int.mul_nonneg h' h'
    rwa [Int.neg_mul_neg] at k

theorem dot_self_num_nonneg (p : Point) : 0 ≤ (dot p p).num := by
  unfold dot Fraction.add Fraction.mul
  exact Int.add_nonneg (Int.mul_nonneg (self_mul_nonneg _) (self_mul_nonneg _))
    (Int.mul_nonneg (self_mul_nonneg _) (self_mul_nonneg _))

private theorem le_add_of_num_nonneg (A B : Fraction) (hA : 0 ≤ A.num) :
    Fraction.le B (Fraction.add A B) := by
  unfold Fraction.le Fraction.add
  dsimp
  have h := Int.mul_nonneg (Int.mul_nonneg hA (Int.le_of_lt B.den_pos)) (Int.le_of_lt B.den_pos)
  have e1 : B.num * (A.den * B.den) = B.num * A.den * B.den := by ac_rfl
  rw [Int.add_mul, e1]
  omega

private theorem le_add_of_num_nonneg' (A B : Fraction) (hB : 0 ≤ B.num) :
    Fraction.le A (Fraction.add A B) := by
  unfold Fraction.le Fraction.add
  dsimp
  have h := Int.mul_nonneg (Int.mul_nonneg hB (Int.le_of_lt A.den_pos)) (Int.le_of_lt A.den_pos)
  have e1 : A.num * (A.den * B.den) = A.num * B.den * A.den := by ac_rfl
  rw [Int.add_mul, e1]
  omega

private theorem le_equiv_trans {x y z : Fraction} (h : Fraction.le x y) (k : Fraction.equiv y z) :
    Fraction.le x z := by
  unfold Fraction.le at *
  unfold Fraction.equiv at k
  have hz := z.den_pos
  have hy := y.den_pos
  have h1 := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hz)
  have h2 : x.num * z.den * y.den ≤ z.num * x.den * y.den := by
    calc x.num * z.den * y.den = x.num * y.den * z.den := by ac_rfl
      _ ≤ y.num * x.den * z.den := h1
      _ = x.den * (y.num * z.den) := by ac_rfl
      _ = x.den * (z.num * y.den) := by rw [k]
      _ = z.num * x.den * y.den := by ac_rfl
  exact Int.le_of_mul_le_mul_right h2 hy

/-- For `w ≥ 0`: `(1 - w*c²)|v|²` never exceeds the invariant. -/
theorem speed_bound (w c : Fraction) (hw : 0 ≤ w.num) (s : Point × Point) :
    Fraction.le (Fraction.mul (margin w c) (dot s.2 s.2)) (invariant w (Fraction.add c c) s) :=
  le_equiv_trans
    (le_add_of_num_nonneg _ _ (Int.mul_nonneg hw (dot_self_num_nonneg _)))
    (Fraction.equiv_symm (invariant_square w c s))

/-- For a nonnegative margin: `w|x + c*v|²` never exceeds the invariant. -/
theorem position_bound (w c : Fraction) (hm : 0 ≤ (margin w c).num) (s : Point × Point) :
    Fraction.le (Fraction.mul w (dot (pointAdd s.1 (pointScale c s.2)) (pointAdd s.1 (pointScale c s.2))))
      (invariant w (Fraction.add c c) s) :=
  le_equiv_trans
    (le_add_of_num_nonneg' _ _ (Int.mul_nonneg hm (dot_self_num_nonneg _)))
    (Fraction.equiv_symm (invariant_square w c s))

/-- Mesh-uniform discrete stability: along every equal-cell schedule of cell
    duration `2c`, `(1 - w*c²)|v_n|²` stays below the **initial** invariant. -/
theorem schedule_speed_bound (w c : Fraction) (hw : 0 ≤ w.num) (n : Nat) (s : Point × Point) :
    Fraction.le
      (Fraction.mul (margin w c)
        (dot (schedule (linearField w) (List.replicate n (Fraction.add c c)) s).2
          (schedule (linearField w) (List.replicate n (Fraction.add c c)) s).2))
      (invariant w (Fraction.add c c) s) :=
  le_equiv_trans (speed_bound w c hw _) (schedule_invariant w (Fraction.add c c) n s)

theorem schedule_position_bound (w c : Fraction) (hm : 0 ≤ (margin w c).num) (n : Nat)
    (s : Point × Point) :
    Fraction.le
      (Fraction.mul w
        (dot (pointAdd (schedule (linearField w) (List.replicate n (Fraction.add c c)) s).1
            (pointScale c (schedule (linearField w) (List.replicate n (Fraction.add c c)) s).2))
          (pointAdd (schedule (linearField w) (List.replicate n (Fraction.add c c)) s).1
            (pointScale c (schedule (linearField w) (List.replicate n (Fraction.add c c)) s).2))))
      (invariant w (Fraction.add c c) s) :=
  le_equiv_trans (position_bound w c hm _) (schedule_invariant w (Fraction.add c c) n s)

end NewtonLimitDynamics.Polygon.HarmonicStability
