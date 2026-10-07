import NewtonLimitDynamics

/-! Controls for Laws Corollaries V and VI, 7 October 2026. Both editions'
theorems are instantiated with an explicit uniform-motion map, vector-addition
update and a two-body spring impulse built from the relative table, so their
premises are satisfiable; the moving space and the common force change the
bodies' absolute states. Two controls show which premises carry the
conclusion. A resistance proportional to each body's velocity measured in the
resting space depends on more than the relative table, and it breaks
Corollary V's conclusion. Collinear relativistic composition with unit limiting
speed changes the velocity differences that Corollary V's "ex hypothesi" step
keeps fixed; vector addition keeps them. -/

namespace NewtonLimitDynamics.Polygon.CommonMotionControls
open NewtonLimitDynamics TimeSubdivision CommonMotion

private def p (x y : Int) : Point := (Fraction.ofInt x, Fraction.ofInt y)
private def half : Fraction := ⟨1, 2, by decide⟩

def motion : Point → Point → Fraction → Point := ZeroForce.inertialAt
def update : Point → Point → Point := pointAdd

theorem inertial1687 : Principia1687.Laws.InertialMotion motion := fun _ _ _ => pointEquiv_refl _
theorem additive1687 : Principia1687.Laws.AdditiveImpulse update := fun _ _ => pointEquiv_refl _
theorem inertial1713 : Principia1713.Laws.InertialMotion motion := fun _ _ _ => pointEquiv_refl _
theorem additive1713 : Principia1713.Laws.AdditiveImpulse update := fun _ _ => pointEquiv_refl _

/-- Each body is pulled toward the other: half the other's relative position. -/
def spring : Nat → (Bool → Bool → State) → Bool → Point :=
  fun _ D i => pointScale half (D (!i) i).1

theorem spring_relative : RelativeKick spring :=
  fun _ _ _ hD i => pointScale_congr half (hD (!i) i).1

def S0 : Bool → State := fun i => if i then (p 2 0, p 0 1) else (p 0 0, p 1 0)
def dt : Nat → Fraction := fun _ => half
def c : Point := p 5 (-3)
def w : Point := p 2 7
def gravity : Nat → Point := fun _ => p 0 (-1)

def free : Nat → (Bool → Bool → State) → Bool → Point → Point :=
  fun k D j v => update v (spring k D j)
def urged : Nat → (Bool → Bool → State) → Bool → Point → Point :=
  fun k D j v => update (update v (spring k D j)) (gravity k)

-- Corollary V, both editions: relative to the moving space, and inter se.
example (n : Nat) (i : Bool) :=
  Principia1687.Laws.corollary5_relative_to_space motion update inertial1687 additive1687
    dt spring spring_relative S0 c w n i
example (n : Nat) (i j : Bool) :=
  Principia1713.Laws.corollary5_motions_inter_se motion update inertial1713 additive1713
    dt spring spring_relative S0 (boost S0 c w) (relative_boost S0 c w) n i j
example (n : Nat) (i j : Bool) :=
  Principia1687.Laws.corollary5_motions_inter_se motion update inertial1687 additive1687
    dt spring spring_relative S0 (boost S0 c w) (relative_boost S0 c w) n i j
-- The moving space really moves the bodies.
example : ¬ pointEquiv (run motion dt free (boost S0 c w) 2 true).1 (run motion dt free S0 2 true).1 := by
  decide
-- Direct evaluation agrees with the theorem at the second boundary.
example : pointEquiv (pointSub (run motion dt free (boost S0 c w) 2 true).1
    (ZeroForce.inertialAt c w (elapsedTime dt 2))) (run motion dt free S0 2 true).1 := by
  decide

-- Corollary VI, both editions: equal motion and unchanged mutual motion.
example (n : Nat) (i : Bool) :=
  Principia1713.Laws.corollary6_equal_motion motion update inertial1713 additive1713
    dt spring spring_relative S0 gravity n i
example (n : Nat) (i j : Bool) :=
  Principia1687.Laws.corollary6_motions_inter_se motion update inertial1687 additive1687
    dt spring spring_relative S0 gravity n i j
-- The common force really changes absolute positions and velocities.
example : ¬ pointEquiv (run motion dt urged S0 2 false).1 (run motion dt free S0 2 false).1 := by
  decide
example : ¬ pointEquiv (run motion dt urged S0 2 false).2 (run motion dt free S0 2 false).2 := by
  decide
example : stateEquiv (relative (run motion dt urged S0 2) true false)
    (relative (run motion dt free S0 2) true false) := by
  unfold stateEquiv; decide

/-- Resistance proportional to velocity in the resting space: halve it. -/
def resisted : Nat → (Bool → Bool → State) → Bool → Point → Point :=
  fun _ _ _ v => pointScale half v

-- Relative to the moving space the velocity differs from the resting case.
example : ¬ pointEquiv
    (pointSub (run motion dt resisted (boost S0 c w) 1 true).2 w)
    (run motion dt resisted S0 1 true).2 := by
  decide

/-- Collinear relativistic composition with unit limiting speed,
`(u + v) / (1 + u v)` over a common denominator. -/
def lorentzAdd (u v : Fraction) (h : 0 < u.den * v.den + u.num * v.num) : Fraction :=
  ⟨u.num * v.den + v.num * u.den, u.den * v.den + u.num * v.num, h⟩

def fsub (a b : Fraction) : Fraction := Fraction.add a ⟨-b.num, b.den, b.den_pos⟩

-- Boosting 1/2 and 0 by 1/2 gives 4/5 and 1/2: the difference changes.
example : ¬ Fraction.equiv
    (fsub (lorentzAdd half half (by decide)) (lorentzAdd (Fraction.ofInt 0) half (by decide)))
    (fsub half (Fraction.ofInt 0)) := by
  decide
-- Vector addition keeps it.
example : Fraction.equiv
    (fsub (Fraction.add half half) (Fraction.add (Fraction.ofInt 0) half))
    (fsub half (Fraction.ofInt 0)) := by
  decide

end NewtonLimitDynamics.Polygon.CommonMotionControls
