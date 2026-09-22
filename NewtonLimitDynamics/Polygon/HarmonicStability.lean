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
    keeps `|v|²` and `w|x + c*v|²` bounded by its initial invariant.  That
    inequality chain is immediate but not formalized here. -/
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

end NewtonLimitDynamics.Polygon.HarmonicStability
