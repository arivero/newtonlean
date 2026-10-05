import NewtonLimitDynamics.Polygon.GeneralForceQuadraticSecants
import BarrowLib.Polygon.TangentTriangleValues

/-! Leading signed doubled tangent-deflection triangle on the actual
constructed sampled Lipschitz central-force curve. Completed determinants
transfer the proved second-order position bound, without assuming an area
expansion. The triangle is distinct from the matched region and its D_mesh. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceTangentTriangle
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicDyadic HarmonicTimeRealization
open ForceClasses GeneralForceEndpoint GeneralForcePrefix GeneralForceTime GeneralForceSecants
open CauchyValues PositionValues SecantValues PairingValues TangentTriangleValues DyadicNodes

def coefficient (T L B : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul L (Fraction.mul (velocityCap T B s) (velocityCap T B s))

theorem coefficient_nonnegative (T L B : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hL : 0 ≤ L.num) (hB : 0 ≤ B.num) :
    0 ≤ (coefficient T L B s).num :=
  Fraction.nonnegative_mul _ _ hL (Fraction.nonnegative_mul _ _
    (velocityCap_nonnegative T B s hT hB) (velocityCap_nonnegative T B s hT hB))

/-- Actual completed triangle/H³ differs from det(v_left,a_left)/2 by
at most H*L*V², including the cell ending at the full endpoint. -/
theorem cell_triangle_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (m k : Nat) (hk : k+1≤blocks m) :
    Within
      (normalizedTriangleValue (duration T m) hT
        (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))
        (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m (k+1))))
      (secantValue (Fraction.ofInt 1).half
        (pairingValue detForm
          (velocityValue (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k)))
          (CompletedForce.forceValue o E0 L hE d.lipschitz d.global_region
            (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))))
        (embed (zeroPoint,zeroPoint)))
      (Fraction.mul (duration T m) (coefficient T L B s)) := by
  rw [normalized_triangle_identity]
  have hs := GeneralForceQuadraticSecants.cell_second_secant_bound o E0 T tau L B s hE d hT m k hk
  rw [GeneralForceQuadraticSecants.cellSecondSecant] at hs
  rw [← node_value o E0 T tau L B s hE d m k,
    ← node_value o E0 T tau L B s hE d m (k+1)] at hs ⊢
  let a := nodeName o E0 T tau L B s hE d m k
  let b := nodeName o E0 T tau L B s hE d m (k+1)
  let v := mapName velocityState velocity_nonexpansive a
  let z := secantName (Fraction.mul (Fraction.ofInt 2) (TimeCalibration.inverse (duration T m) hT))
    (secantName (TimeCalibration.inverse (duration T m) hT) b a) v
  let f := CompletedForce.forceName o E0 L hE d.lipschitz d.global_region a
  let V := velocityCap T B s
  let R := Fraction.mul (Fraction.ofInt 2) (Fraction.mul L (Fraction.mul (duration T m) V))
  have hV := velocityCap_nonnegative T B s d.time_nonnegative d.bound_nonnegative
  have hv : ∀ j : Nat, 0≤j → Fraction.le (pointNorm (v.approx j).1) V := by
    intro j _
    change Fraction.le (pointNorm (a.approx j).2) V
    rw [node_approx o E0 T tau L B s hE d m k (by omega) j]
    apply GeneralForcePrefix.count_velocity o E0 T tau L B s hE d (m+j) (k*blocks j)
    rw [blocks_add]
    exact Nat.mul_le_mul_right (blocks j) (by omega)
  have hz : NameBound z f R := hs
  have hp := pairing_name_bound_right detForm v z f V R hV 0 hv hz
  let q := (Fraction.ofInt 1).half
  have hq : 0 ≤ q.num := by decide
  have hb := nameBound_scale
    (secantName q (pairingName detForm v z) (constantName (zeroPoint,zeroPoint)))
    (secantName q (pairingName detForm v f) (constantName (zeroPoint,zeroPoint)))
    (pairingName detForm v z) (pairingName detForm v f) q.abs (Fraction.mul R V)
    (Fraction.abs_num_nonnegative q) (fun j => by
      have hlevel := secant_distance_bound q
        ((pairingName detForm v z).approx j) (zeroPoint,zeroPoint)
        ((pairingName detForm v f).approx j) (zeroPoint,zeroPoint)
      apply Fraction.le_equiv_right hlevel
      apply Fraction.equiv_trans (Fraction.mul_equiv (Fraction.equiv_refl _)
        (Fraction.add_equiv (Fraction.equiv_refl _) (FiniteEstimates.stateDistance_self_zero _)))
      simp only [Fraction.equiv,Fraction.mul,Fraction.add,Fraction.ofInt,
        Int.zero_mul,Int.mul_zero,Int.zero_add,Int.add_zero,Int.one_mul,Int.mul_one]
      ac_nf) hp
  apply nameBound_mono _ _ _ _ (Fraction.le_of_equiv ?_) hb
  rw [Fraction.abs_eq_of_nonnegative q hq]
  simp only [R,V,q,coefficient,Fraction.equiv,Fraction.mul,Fraction.half,Fraction.ofInt,
    Int.mul_one,Int.one_mul]
  ac_nf

/-- Uniform leading signed doubled triangle on all constructed dyadic cells.
Unsigned triangle area has half the absolute doubled-area value; lobe and
matched-region area require their own geometric identifications. -/
theorem normalized_triangles_converge (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (hT : 0 < T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ k, k+1≤blocks m →
      Within
        (normalizedTriangleValue (duration T m) hT
          (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))
          (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m (k+1))))
        (secantValue (Fraction.ofInt 1).half
          (pairingValue detForm
            (velocityValue (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k)))
            (CompletedForce.forceValue o E0 L hE d.lipschitz d.global_region
              (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))))
          (embed (zeroPoint,zeroPoint))) eps := by
  have hC := coefficient_nonnegative T L B s d.time_nonnegative d.lipschitz.1 d.bound_nonnegative
  obtain ⟨N,hN⟩ := duration_eventually_small (Fraction.mul T (coefficient T L B s)) eps
    (Fraction.nonnegative_mul _ _ d.time_nonnegative hC) heps
  refine ⟨N,fun m hm k hk => within_mono _ _ _ _ ?_
    (cell_triangle_bound o E0 T tau L B s hE d hT m k hk)⟩
  apply Fraction.le_equiv_left (b := duration (Fraction.mul T (coefficient T L B s)) m)
    _ (Fraction.magnitudes.lt_implies_le (hN m hm))
  simp only [duration,Fraction.equiv,Fraction.mul]
  ac_nf

end NewtonLimitDynamics.Polygon.GeneralForceTangentTriangle
