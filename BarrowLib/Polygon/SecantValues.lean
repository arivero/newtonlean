import BarrowLib.Polygon.PositionValues
import BarrowLib.Polygon.ScaledTolerance

/-! Rationally scaled position differences and velocity projections of
constructed Cauchy values. All Cauchy and representative-invariance proofs
precede quotient lifting; no rate-of-change premise is supplied. -/

namespace NewtonLimitDynamics.Polygon.SecantValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic CauchyValues PositionValues
open FiniteEstimates HarmonicTimeRealization

def pointState (p : Point) : Point × Point := (p,zeroPoint)
def velocityState (s : Point × Point) : Point × Point := pointState s.2

theorem pointState_distance (p q : Point) :
    Fraction.equiv (distance (pointState p) (pointState q)) (pointDistance p q) :=
  Fraction.equiv_trans (Fraction.add_equiv (Fraction.equiv_refl _)
    (pointDistance_self_zero zeroPoint)) (Fraction.add_zero _)

theorem velocity_nonexpansive (s t : Point × Point) :
    Fraction.le (distance (velocityState s) (velocityState t)) (distance s t) :=
  Fraction.le_equiv_left (pointState_distance s.2 t.2) (velocity_le_state (stateSub s t))

def velocityValue : Value → Value := mapValue velocityState velocity_nonexpansive

theorem velocityValue_within (x y : Value) (R : Fraction) (h : Within x y R) :
    Within (velocityValue x) (velocityValue y) R := mapValue_within _ velocity_nonexpansive x y R h

theorem velocityValue_embed (s : Point × Point) :
    velocityValue (embed s) = embed (velocityState s) := mapValue_embed _ velocity_nonexpansive s

def secantState (q : Fraction) (s t : Point × Point) : Point × Point :=
  pointState (pointScale q (pointSub s.1 t.1))

theorem secant_distance_bound (q : Fraction) (a b c d : Point × Point) :
    Fraction.le (distance (secantState q a b) (secantState q c d))
      (Fraction.mul q.abs (Fraction.add (distance a c) (distance b d))) := by
  have hp := Fraction.magnitudes.le_trans (difference_sub_bound a.1 c.1 b.1 d.1)
    (Fraction.add_le_add (point_le_state (stateSub a c)) (point_le_state (stateSub b d)))
  exact Fraction.le_equiv_left (Fraction.equiv_trans (pointState_distance _ _)
    (difference_scale q _ _))
    (Fraction.mul_le_mul_nonnegative_left hp q.abs (Fraction.abs_num_nonnegative q))

theorem two_scaled_small (q eps r s : Fraction) (_heps : 0 < eps.num)
    (hr : 0 ≤ r.num) (hs : 0 ≤ s.num)
    (h1 : Fraction.lt r (factorDelta q.abs eps.half (Fraction.abs_num_nonnegative q)))
    (h2 : Fraction.lt s (factorDelta q.abs eps.half (Fraction.abs_num_nonnegative q))) :
    Fraction.lt (Fraction.mul q.abs (Fraction.add r s)) eps := by
  have ha := factor_control q.abs eps.half r (Fraction.abs_num_nonnegative q) hr h1
  have hb := factor_control q.abs eps.half s (Fraction.abs_num_nonnegative q) hs h2
  have hc := Fraction.add_lt_add ha hb
  have he := Fraction.half_add_self eps
  have hd := lt_equiv_right hc he
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (Fraction.equiv_trans (Fraction.mul_comm _ _) (Fraction.add_mul _ _ _))) hd

def secantName (q : Fraction) (a b : EndpointCauchyName) : EndpointCauchyName where
  approx := fun n => secantState q (a.approx n) (b.approx n)
  cauchy := by
    intro eps heps
    let delta := factorDelta q.abs eps.half (Fraction.abs_num_nonnegative q)
    have hd : 0 < delta.num := factorDelta_positive _ _ _ heps
    obtain ⟨N,hN⟩ := a.cauchy delta hd
    obtain ⟨M,hM⟩ := b.cauchy delta hd
    refine ⟨max N M,fun m n hm hn => ?_⟩
    exact Fraction.magnitudes.lt_of_le_lt (secant_distance_bound q _ _ _ _)
      (two_scaled_small q eps _ _ heps (stateNorm_nonnegative _) (stateNorm_nonnegative _)
        (hN m n (by omega) (by omega)) (hM m n (by omega) (by omega)))

theorem secantName_equiv (q : Fraction) (a b a' b' : EndpointCauchyName)
    (ha : NameEquiv a a') (hb : NameEquiv b b') :
    NameEquiv (secantName q a b) (secantName q a' b') := by
  intro eps heps
  let delta := factorDelta q.abs eps.half (Fraction.abs_num_nonnegative q)
  have hd : 0 < delta.num := factorDelta_positive _ _ _ heps
  obtain ⟨N,hN⟩ := ha delta hd
  obtain ⟨M,hM⟩ := hb delta hd
  refine ⟨max N M,fun n hn => ?_⟩
  exact Fraction.magnitudes.lt_of_le_lt (secant_distance_bound q _ _ _ _)
    (two_scaled_small q eps _ _ heps (stateNorm_nonnegative _) (stateNorm_nonnegative _)
      (hN n (by omega)) (hM n (by omega)))

def secantValue (q : Fraction) (x y : Value) : Value :=
  Quotient.liftOn₂ x y (fun a b => realize (secantName q a b))
    (fun a b a' b' ha hb => Quotient.sound (secantName_equiv q a b a' b' ha hb))

theorem secantValue_realize (q : Fraction) (a b : EndpointCauchyName) :
    secantValue q (realize a) (realize b) = realize (secantName q a b) := rfl

theorem secantValue_embed (q : Fraction) (s t : Point × Point) :
    secantValue q (embed s) (embed t) = embed (secantState q s t) := rfl

def shiftedName (a : EndpointCauchyName) (m : Nat) : EndpointCauchyName where
  approx := fun j => a.approx (m+j)
  cauchy := by
    intro eps heps
    obtain ⟨N,hN⟩ := a.cauchy eps heps
    exact ⟨N,fun i j hi hj => hN (m+i) (m+j) (by omega) (by omega)⟩

theorem shiftedName_equiv (a : EndpointCauchyName) (m : Nat) : NameEquiv (shiftedName a m) a := by
  intro eps heps
  obtain ⟨N,hN⟩ := a.cauchy eps heps
  exact ⟨N,fun j hj => hN (m+j) j (by omega) hj⟩

theorem shiftedValue (a : EndpointCauchyName) (m : Nat) : realize (shiftedName a m) = realize a :=
  Quotient.sound (shiftedName_equiv a m)

end NewtonLimitDynamics.Polygon.SecantValues
