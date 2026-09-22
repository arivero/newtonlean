import NewtonLimitDynamics.Polygon.ZeroForce

namespace NewtonLimitDynamics.Polygon.InertialControl

open NewtonLimitDynamics
open TimeSubdivision
open ZeroForce

/-- Strict comparison of the absolute value of a represented rational with a
    positive rational. It is cross multiplication, so it tolerates unnormalised
    representatives. -/
def absLt (a bound : Fraction) : Prop :=
  (a.num.natAbs : Int) * bound.den < bound.num * a.den

/-- A common positive integer bound for both velocity numerators. -/
def velocityBound (v : Point) : Nat :=
  v.1.num.natAbs + v.2.num.natAbs + 1

/-- An explicit time radius, for an arbitrary fixed rational velocity. -/
def radius (eps : Fraction) (v : Point) : Fraction :=
  ⟨eps.num, eps.den * (velocityBound v : Int),
    Int.mul_pos eps.den_pos (by
      unfold velocityBound
      exact Int.ofNat_pos.mpr (by omega))⟩

theorem radius_positive (eps : Fraction) (v : Point)
    (heps : Fraction.positive eps) : Fraction.positive (radius eps v) := heps

private theorem scalar_bound (eps h x : Fraction) (K : Nat)
    (heps : Fraction.positive eps) (hK : x.num.natAbs < K)
    (hh : absLt h ⟨eps.num, eps.den * (K : Int),
      Int.mul_pos eps.den_pos (Int.ofNat_pos.mpr (by omega))⟩) :
    absLt (Fraction.mul h x) eps := by
  have hK' : (x.num.natAbs : Int) ≤ K := Int.ofNat_le.mpr (Nat.le_of_lt hK)
  have hden : 1 ≤ x.den := by
    have := x.den_pos
    omega
  have hleft : 0 ≤ (h.num.natAbs : Int) * eps.den :=
    Int.mul_nonneg (Int.ofNat_zero_le _) (Int.le_of_lt eps.den_pos)
  have hmul := Int.mul_le_mul_of_nonneg_left hK' hleft
  have hright : 0 ≤ eps.num * h.den :=
    Int.mul_nonneg (Int.le_of_lt heps) (Int.le_of_lt h.den_pos)
  have hdenmul := Int.mul_le_mul_of_nonneg_left hden hright
  have hsmall : (h.num.natAbs : Int) * eps.den * (K : Int) < eps.num * h.den := by
    unfold absLt at hh
    dsimp at hh
    simpa only [Int.mul_assoc] using hh
  have hchain : (h.num.natAbs : Int) * (x.num.natAbs : Int) * eps.den <
      eps.num * (h.den * x.den) := by
    calc
      (h.num.natAbs : Int) * (x.num.natAbs : Int) * eps.den
          = ((h.num.natAbs : Int) * eps.den) * (x.num.natAbs : Int) := by ac_rfl
      _ ≤ ((h.num.natAbs : Int) * eps.den) * (K : Int) := hmul
      _ < eps.num * h.den := hsmall
      _ ≤ (eps.num * h.den) * x.den := by simpa using hdenmul
      _ = eps.num * (h.den * x.den) := by ac_rfl
  unfold absLt Fraction.mul
  dsimp
  rw [Int.natAbs_mul]
  exact hchain

/-- For each positive rational tolerance, one explicit radius controls both
    coordinates of every rational drift at fixed velocity. -/
theorem drift_small (eps : Fraction) (v : Point)
    (heps : Fraction.positive eps) (h : Fraction)
    (hh : absLt h (radius eps v)) :
    absLt (pointScale h v).1 eps ∧ absLt (pointScale h v).2 eps := by
  have hK1 : v.1.num.natAbs < velocityBound v := by
    unfold velocityBound
    omega
  have hK2 : v.2.num.natAbs < velocityBound v := by
    unfold velocityBound
    omega
  constructor
  · exact scalar_bound eps h v.1 (velocityBound v) heps hK1 hh
  · exact scalar_bound eps h v.2 (velocityBound v) heps hK2 hh

/-- The controlled drift is the increment in the rational inertial map at
    every rational base time. This is an equivalence of represented positions,
    not an assumed curve or a limit theorem. -/
theorem inertialAt_small_increment (eps : Fraction) (p v : Point)
    (heps : Fraction.positive eps) (t h : Fraction)
    (hh : absLt h (radius eps v)) :
    pointEquiv (inertialAt (inertialAt p v t) v h)
      (inertialAt p v (Fraction.add t h)) ∧
    absLt (pointScale h v).1 eps ∧ absLt (pointScale h v).2 eps := by
  exact ⟨inertialAt_add p v t h, drift_small eps v heps h hh⟩

/-- The same estimate applies to an actual zero-force end-kick cell begun at
    any rational inertial time. -/
theorem endKick_zero_small_increment (eps : Fraction) (p v : Point)
    (heps : Fraction.positive eps) (t h : Fraction)
    (hh : absLt h (radius eps v)) :
    pointEquiv (endKick h (inertialAt p v t, v) zeroPoint).1
      (inertialAt p v (Fraction.add t h)) ∧
    absLt (pointScale h v).1 eps ∧ absLt (pointScale h v).2 eps := by
  have hcell := (endKick_zero h (inertialAt p v t, v)).1
  have hmap := inertialAt_add p v t h
  exact ⟨⟨Fraction.equiv_trans hcell.1 hmap.1,
    Fraction.equiv_trans hcell.2 hmap.2⟩, drift_small eps v heps h hh⟩

/-- Quantified small-time form. The witness is `radius eps v`, independent of
    the base time and initial position. -/
theorem exists_uniform_inertial_radius (eps : Fraction) (v : Point)
    (heps : Fraction.positive eps) :
    ∃ delta : Fraction, Fraction.positive delta ∧
      ∀ (p : Point) (t h : Fraction), absLt h delta →
        pointEquiv (inertialAt (inertialAt p v t) v h)
          (inertialAt p v (Fraction.add t h)) ∧
        absLt (pointScale h v).1 eps ∧ absLt (pointScale h v).2 eps := by
  exact ⟨radius eps v, radius_positive eps v heps,
    fun p t h hh => inertialAt_small_increment eps p v heps t h hh⟩

end NewtonLimitDynamics.Polygon.InertialControl
