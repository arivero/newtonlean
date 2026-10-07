import Reverse.Classical.ClassicalTrajectory
import Reverse.NonRelativistic.ZeroInvCFibre
import Reverse.Newton.Interface

/-!
PHYSICAL STAGE:
  Newton's Law I and Law II shapes derived from the centre-of-mass
  assumptions, and the consistency of the classical velocity with the
  zero-invC fibre's kinetic energy.
MATHEMATICAL CONTENT:
  From (1) localized trajectories, (2) conserved momentum with uniform
  increments and (3) p = m v: the drift q(t) = q + t v. From (3) and (4)
  additive impulses on momenta: the additive calibrated velocity update.
  The two together inhabit `NewtonInterface`.
INPUT PARAMETERS:
  Masses of the composites.
OUTPUT PARAMETERS:
  A `NewtonInterface` per body.
PROVED HERE:
  `motion_inertial`, `update_additive`, `newtonInterface`;
  `velocity_eq_momentum_over_mass`; `kinetic_half_momentum_velocity`: on
  the fibre, K = ½ p · v with the velocity of (3), so the classical
  velocity relation agrees with the derived kinetic energy.
ASSUMED HERE:
  Nothing beyond (1)–(4) and the fibre.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/Chain.lean`, then `Reverse/Principia`.

STATUS: theorem (formal consequences of the stated assumptions).
-/

namespace Reverse.Classical
open Reverse.Parent Reverse.Matter Reverse.RelativisticQM Reverse.NonRelativistic Reverse.Newton
open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.TimeSubdivision

variable {I : MatterInputs} {M : HasStableNeutralMatter I}
  {T : HasLocalizedCOMTrajectory M} {D : HasFreeCOMDynamics T}

/-- The inverse mass of a body, the mass of the composite. -/
def inverseMass (M : HasStableNeutralMatter I) (b : M.Body) : Scalar :=
  Fraction.quotient (Fraction.ofInt 1) (M.body b).mass (M.body b).mass_positive

theorem scale_inverse_cancel (M : HasStableNeutralMatter I) (b : M.Body) (x : Point) :
    pointEquiv (pointScale (M.body b).mass (pointScale (inverseMass M b) x)) x := by
  constructor <;>
    simp only [pointScale, inverseMass, Fraction.equiv, Fraction.mul, Fraction.quotient,
      Fraction.ofInt, Int.one_mul, Int.mul_one] <;> ac_nf

/-- Zero time is a left identity for rational time values. -/
theorem zero_add_time (t : Fraction) :
    Fraction.equiv t (Fraction.add (Fraction.ofInt 0) t) :=
  Fraction.equiv_symm
    (Fraction.equiv_trans (Fraction.add_comm (Fraction.ofInt 0) t) (Fraction.add_zero t))

/-- Law I shape: the body released at q with velocity v, hence momentum m v,
followed along its free trajectory. -/
def motion (_R : HasMomentumVelocityRelation D) (b : M.Body) (q v : Point)
    (t : Fraction) : Point :=
  T.position b q (pointScale (M.body b).mass v) t

/-- The free trajectory is the uniform rectilinear drift. -/
theorem motion_inertial (R : HasMomentumVelocityRelation D) (b : M.Body) (q v : Point)
    (t : Fraction) : pointEquiv (motion R b q v t) (ZeroForce.inertialAt q v t) := by
  have h1 := T.position_time_congr b q (pointScale (M.body b).mass v) (zero_add_time t)
  have h2 := D.uniform_increment b q (pointScale (M.body b).mass v) (Fraction.ofInt 0) t
  have h3 : pointEquiv
      (D.velocity b (T.momentum b q (pointScale (M.body b).mass v) (Fraction.ofInt 0))) v :=
    pointEquiv_trans
      (R.velocity_congr b (D.momentum_conserved b q (pointScale (M.body b).mass v) _))
      (R.velocity_of_momentum b v)
  have h4 := pointAdd_congr (T.position_initial b q (pointScale (M.body b).mass v))
    (pointScale_congr t h3)
  exact pointEquiv_trans h1 (pointEquiv_trans h2 h4)

/-- Law II shape: the velocity after an impulse, computed on momenta. The
second argument is the calibrated velocity change, as in the historical
predicates. -/
def update (_R : HasMomentumVelocityRelation D) (J : HasImpulseDynamics M) (b : M.Body)
    (u w : Point) : Point :=
  D.velocity b (J.kick b (pointScale (M.body b).mass u) (pointScale (M.body b).mass w))

/-- Additive momenta and p = m v give additive calibrated velocity changes. -/
theorem update_additive (R : HasMomentumVelocityRelation D) (J : HasImpulseDynamics M)
    (b : M.Body) (u w : Point) : pointEquiv (update R J b u w) (pointAdd u w) := by
  have h1 := R.velocity_congr b (J.momentum_additive b
    (pointScale (M.body b).mass u) (pointScale (M.body b).mass w))
  have h2 := R.velocity_congr b (pointEquiv_symm (pointScale_add (M.body b).mass u w))
  exact pointEquiv_trans h1 (pointEquiv_trans h2 (R.velocity_of_momentum b (pointAdd u w)))

/-- The Newton interface of one body, derived from (1)–(4). -/
def newtonInterface (R : HasMomentumVelocityRelation D) (J : HasImpulseDynamics M)
    (b : M.Body) : NewtonInterface where
  motion := motion R b
  update := update R J b
  inertial := motion_inertial R b
  additive := update_additive R J b

/-- The velocity map is p/m. -/
theorem velocity_eq_momentum_over_mass (R : HasMomentumVelocityRelation D) (b : M.Body)
    (p : Point) : pointEquiv (D.velocity b p) (pointScale (inverseMass M b) p) :=
  pointEquiv_trans
    (R.velocity_congr b (pointEquiv_symm (scale_inverse_cancel M b p)))
    (R.velocity_of_momentum b (pointScale (inverseMass M b) p))

/-- Euclidean inner product of coordinate vectors. -/
def dot (a c : Point) : Scalar :=
  Fraction.add (Fraction.mul a.1 c.1) (Fraction.mul a.2 c.2)

theorem dot_congr_right (a : Point) {c c' : Point} (h : pointEquiv c c') :
    Fraction.equiv (dot a c) (dot a c') :=
  Fraction.add_equiv (Fraction.mul_equiv_left a.1 h.1) (Fraction.mul_equiv_left a.2 h.2)

theorem half_congr {a b : Fraction} (h : Fraction.equiv a b) :
    Fraction.equiv a.half b.half := by
  simp only [Fraction.equiv, Fraction.half] at h ⊢
  calc a.num * (2 * b.den) = 2 * (a.num * b.den) := by ac_rfl
    _ = 2 * (b.num * a.den) := by rw [h]
    _ = b.num * (2 * a.den) := by ac_rfl

/-- Half of p · (p/m) is p²/(2m): the algebraic identity behind the
consistency theorem. -/
theorem half_dot_inverse (M : HasStableNeutralMatter I) (b : M.Body) (p : Point) :
    Fraction.equiv
      (Fraction.quotient (normSq p) (twice (M.body b).mass)
        (twice_positive (M.body b).mass_positive))
      (Fraction.half (dot p (pointScale (inverseMass M b) p))) := by
  simp only [Fraction.equiv, Fraction.quotient, Fraction.half, Fraction.mul, Fraction.add,
    Fraction.ofInt, normSq, dot, pointScale, twice, inverseMass, Int.one_mul, Int.mul_one,
    Int.add_mul, Int.mul_add]
  ac_nf

/-- On the fibre the kinetic energy is ½ p · v with the velocity of (3): the
classical momentum–velocity relation is consistent with the derived
kinetic energy. -/
theorem kinetic_half_momentum_velocity {S : StableParticleSector M} (Z : HasZeroInvCFibre S)
    (R : HasMomentumVelocityRelation D) (b : M.Body) (p : Point) :
    Fraction.equiv (Z.fibre.kinetic b p) (Fraction.half (dot p (D.velocity b p))) :=
  Fraction.equiv_trans (kinetic_energy_on_fibre Z b p)
    (Fraction.equiv_trans (half_dot_inverse M b p)
      (Fraction.equiv_symm (half_congr (dot_congr_right p (velocity_eq_momentum_over_mass R b p)))))

end Reverse.Classical
