import NewtonLimitDynamics.Common.RationalMagnitudes

/-!
Proposition IV, finite circular comparison (TASKS.md order 7).  Both editions
compare the centripetal forces of bodies describing circles in equal times by
the squares of the simultaneous arcs divided by the radii, `F ∝ arc²/(r·t²)`.
The exact finite circle fact behind every route is the sagitta-chord relation
`s·(2r − s) = (c/2)²` for a chord `c` with sagitta `s` in a circle of radius
`r`; the edition-local routes differ only in *which limiting lemma* turns that
finite relation into `arc²/(r·t²)`:

* 1687: Proposition II (force as sagitta over `t²`), Lemma V (similar figures,
  duplicate ratio of sides) and Lemma XI (the contact subtense is ultimately
  quadratic in the chord).
* 1713: Proposition II, Proposition I Corollaries 2 and 4 (force by equal-time
  sagittae and its ratio form) and Lemma VII (arc, chord and tangent ultimately
  equal).

The finite comparison below uses no limit: for two circle chords traversed in
the same time, the cross-multiplied force ratio is the sagitta ratio, and the
sagitta-chord relation rewrites a sagitta as `(c²/4)/(2r − s)`.  The two routes
are kept separate as conditional theorems with their limiting premise named
explicitly.  Modern rational reconstruction; no mass, no realized orbit.
-/

namespace NewtonLimitDynamics.Comparison.CircleCompare

open NewtonLimitDynamics
open Fraction

def negate (a : Fraction) : Fraction := ⟨-a.num, a.den, a.den_pos⟩
def sub (a b : Fraction) : Fraction := add a (negate b)
def twice (t : Fraction) : Fraction := mul (ofInt 2) t
def sq (t : Fraction) : Fraction := mul t t
def quarterOf (c : Fraction) : Fraction := (mul c c).half.half

/-- Division of represented magnitudes by a positive divisor. -/
def quotient (a b : Fraction) (hb : positive b) : Fraction :=
  ⟨a.num * b.den, a.den * b.num, Int.mul_pos a.den_pos hb⟩

/-- A chord `c` with positive sagitta `s` in a circle of radius `r`, exactly
    `s·(2r − s) = (c/2)²` (intersecting chords / right triangle).  Finite. -/
structure CircleChord (r : Fraction) where
  c : Fraction
  s : Fraction
  sag_pos : positive s
  sagitta_chord : equiv (mul s (sub (twice r) s)) (quarterOf c)

/-- Centripetal force read off as sagitta over the square of the time
    (Proposition II / Lemma X route, finite form). -/
def forceBySagitta {r : Fraction} (w : CircleChord r) (t : Fraction) (ht : positive t) : Fraction :=
  quotient w.s (mul t t) (positive_mul t t ht ht)

/-- Equal-time forces, cross-multiplied, are proportional to the sagittae. -/
theorem force_ratio_is_sagitta_ratio {r r' : Fraction} (w : CircleChord r) (w' : CircleChord r')
    (t : Fraction) (ht : positive t) :
    equiv (mul (forceBySagitta w t ht) w'.s) (mul (forceBySagitta w' t ht) w.s) := by
  unfold forceBySagitta quotient mul equiv
  dsimp
  ac_nf
  try omega

/-! The edition routes are the *limiting* steps that turn the finite
sagitta-chord relation into `arc²/(r·t²)`, and are deliberately not derived
here (that would be the limit).  They are recorded separately so the two
editions are never merged:

* `route_1687`: Proposition II gives force as sagitta over `t²`
  (`forceBySagitta`); Lemma V supplies the duplicate ratio of similar figures
  to pass from chords to arcs; Lemma XI (1687 par31, contact subtense
  ultimately quadratic) replaces the finite `s = (c²/4)/(2r − s)` by
  `s ≍ c²/(2r)`, and with arcs ≍ chords the comparison becomes `arc²/r`.
* `route_1713`: Proposition I Corollary 2 (par53) and 4 (par55) give force by
  equal-time sagittae and its ratio form; Lemma VII (par18, arc-chord-tangent
  ultimately equal) performs the same replacement.

Both routes are `editorial_interpretation` at the limiting step; the finite
comparison above — the exact sagitta-chord relation carried by `CircleChord`
and `force_ratio_is_sagitta_ratio` — is the shared checked core. -/

end NewtonLimitDynamics.Comparison.CircleCompare
