import ModernLib.Polygon.GeneralForceQuadraticSecants
import ModernLib.Polygon.HarmonicCompletedForce
import ModernLib.Foundation.Polygon.QuadraticPotentialValues

/-! The harmonic polynomial potential evaluated at the actual constructed
curve and its tangent continuation. Its normalized per-cell drop tends to
-m*dot(a,a)/2. Finite second-order and half-mesh errors are retained until
proved vanishing. This law test does not construct general radial potentials
or identify the deflection triangle with D_mesh. -/

namespace NewtonLimitDynamics.Diagnostic.ConstructedHarmonicPotential
open NewtonLimitDynamics
open Polygon
open TimeSubdivision PointBounds FiniteEstimates HarmonicStability HarmonicDyadic
open HarmonicTimeComparison HarmonicComparison CauchyValues PositionValues SecantValues
open PairingValues QuadraticPotentialValues DyadicNodes BinaryTime HarmonicTimeRealization
open ForceClasses GeneralForceEndpoint GeneralForceSecants

/-- Finite work identifies the polynomial with the linear central force:
the residual after -mass*a(p) dot (q-p) is the quadratic displacement term. -/
theorem finite_work_remainder (mass w : Fraction) (p q : Point) :
    Fraction.equiv
      (Fraction.add
        (durationDifference (quadratic (Fraction.mul mass w).half p)
          (quadratic (Fraction.mul mass w).half q))
        (Fraction.mul mass (dot (linearField w p) (pointSub q p))))
      (Fraction.mul (Fraction.mul mass w).half (dot (pointSub q p) (pointSub q p))) := by
  simp only [quadratic,durationDifference,linearField,negF,dot,pointSub,pointNeg,
    pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.half,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
  simp only [show (2 : Int)=1+1 by rfl,Int.add_mul,Int.mul_add,Int.one_mul,Int.mul_one]
  ac_nf <;> omega

private structure Frame where
  P : Fraction
  V : Fraction
  A : Fraction
  U : Fraction
  Z : Fraction

private def frame (w T : Fraction) (s : Point × Point) : Frame :=
  let P := Fraction.mul (Fraction.ofInt 2) (stateNorm s)
  let V := velocityCap T (HarmonicGeneralEndpoint.harmonicBound w s) s
  let A := Fraction.mul w.abs P
  let U := Fraction.mul (Fraction.ofInt 2) (Fraction.mul w.abs V)
  ⟨P,V,A,U,Fraction.add A (Fraction.add (Fraction.mul T U) A)⟩

private theorem frame_nonnegative (w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num) :
    0 ≤ (frame w T s).P.num ∧ 0 ≤ (frame w T s).V.num ∧ 0 ≤ (frame w T s).A.num ∧
      0 ≤ (frame w T s).U.num ∧ 0 ≤ (frame w T s).Z.num := by
  have hP := Fraction.nonnegative_mul (Fraction.ofInt 2) (stateNorm s) (by decide) (stateNorm_nonnegative s)
  have hV := velocityCap_nonnegative T (HarmonicGeneralEndpoint.harmonicBound w s) s hT
    (HarmonicGeneralEndpoint.harmonicBound_nonnegative w s)
  have hA := Fraction.nonnegative_mul w.abs _ (Fraction.abs_num_nonnegative w) hP
  have hU := Fraction.nonnegative_mul (Fraction.ofInt 2) _ (by decide)
    (Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative w) hV)
  exact ⟨hP,hV,hA,hU,Fraction.nonnegative_add _ _ hA
    (Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hT hU) hA)⟩

def coefficient (mass w T : Fraction) (s : Point × Point) : Fraction :=
  let f := frame w T s
  remainderCoefficient (Fraction.mul mass w).half T f.P f.V f.Z f.U

theorem coefficient_nonnegative (mass w T : Fraction) (s : Point × Point) (hT : 0 ≤ T.num) :
    0 ≤ (coefficient mass w T s).num := by
  obtain ⟨hP,hV,_,hU,hZ⟩ := frame_nonnegative w T s hT
  exact remainderCoefficient_nonnegative _ _ _ _ _ _ hT hP hV hZ hU

/-- The Euclidean squared acceleration is the dot product, rather than the
coordinate L1 gauge used to bound errors. -/
def forceEnergyValue (mass : Fraction) (a : Value) : Value :=
  secantValue (negF mass.half) (pairingValue dotForm a a) (embed (zeroPoint,zeroPoint))

private def workName (mass w : Fraction) (a : EndpointCauchyName) : EndpointCauchyName :=
  secantName (Fraction.mul mass w).half
    (pairingName dotForm (secantName (negF w) a (constantName (zeroPoint,zeroPoint))) a)
    (constantName (zeroPoint,zeroPoint))

private theorem work_approximant (mass w : Fraction) (a : EndpointCauchyName) (j : Nat) :
    stateEquiv ((workName mass w a).approx j)
      (scalarState (Fraction.mul (Fraction.mul mass w).half
        (dot (linearField w (a.approx j).1) (a.approx j).1))) := by
  let g := secantName (negF w) a (constantName (zeroPoint,zeroPoint))
  have he := scaled_pairing_approximant dotForm (Fraction.mul mass w).half g a j
  have hg : pointEquiv (g.approx j).1 (linearField w (a.approx j).1) :=
    pointScale_congr (negF w) (pointSub_zero _)
  exact ⟨⟨Fraction.equiv_trans he.1.1 (Fraction.mul_equiv_left _
    (dot_congr hg ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)),he.1.2⟩,he.2⟩

theorem force_work_eq_energy (mass w : Fraction) (x : Value) :
    secantValue (Fraction.mul mass w).half
      (pairingValue dotForm (HarmonicCompletedForce.linearValue w x) x) (embed (zeroPoint,zeroPoint)) =
      forceEnergyValue mass (HarmonicCompletedForce.linearValue w x) := by
  induction x using Quotient.inductionOn with
  | _ a =>
    apply Quotient.sound
    apply nameEquiv_of_levelwise_stateEquiv
    intro j
    have hzero : zeroPoint=(Fraction.ofInt 0,Fraction.ofInt 0) := rfl
    have hscalar : ∀ q, scalarState q=((q,Fraction.ofInt 0),(Fraction.ofInt 0,Fraction.ofInt 0)) := fun _ => rfl
    constructor
    · constructor <;>
        simp only [forceEnergyValue,HarmonicCompletedForce.linearValue,secantName,secantState,
          pointState,pairingName,BinaryLift.name,secantOperation,pairingOperation,
          pairingState,dotForm,constantName,hscalar,hzero,dot,
          pointEquiv,pointSub,pointNeg,pointAdd,pointScale,negF,Fraction.equiv,Fraction.add,
          Fraction.mul,Fraction.half,Fraction.ofInt,Int.add_mul,Int.mul_add,Int.neg_mul,
          Int.mul_neg,Int.one_mul,Int.mul_one,Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add,
          Int.neg_zero] <;> ac_nf <;> omega
    · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩

private theorem node_frame_bounds (w T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (ht : 0 < T.num)
    (m k : Nat) (hk : k+1≤blocks m) (j : Nat) :
    let d := HarmonicGeneralTime.conditions w (Fraction.ofInt 1) T s hw (by decide) hT hs
    let a := nodeName (harmonicOracle w hw) (Fraction.ofInt 1) T (Fraction.ofInt 1) w.abs
      (HarmonicGeneralEndpoint.harmonicBound w s) s (by decide) d m k
    let b := nodeName (harmonicOracle w hw) (Fraction.ofInt 1) T (Fraction.ofInt 1) w.abs
      (HarmonicGeneralEndpoint.harmonicBound w s) s (by decide) d m (k+1)
    let z := (QuadraticSecants.secondState (duration T m) ht (a.approx j) (b.approx j)).1
    let f := frame w T s
    Fraction.le (pointNorm (a.approx j).1) f.P ∧
      Fraction.le (pointNorm (a.approx j).2) f.V ∧
      Fraction.le (pointNorm z) f.Z ∧
      Fraction.le (pointDistance z (linearField w (a.approx j).1))
        (Fraction.add (Fraction.mul (duration T m) f.U)
          (Fraction.mul (duration (Fraction.ofInt 1) j) f.A)) := by
  let d := HarmonicGeneralTime.conditions w (Fraction.ofInt 1) T s hw (by decide) hT hs
  let a := nodeName (harmonicOracle w hw) (Fraction.ofInt 1) T (Fraction.ofInt 1) w.abs
    (HarmonicGeneralEndpoint.harmonicBound w s) s (by decide) d m k
  let b := nodeName (harmonicOracle w hw) (Fraction.ofInt 1) T (Fraction.ofInt 1) w.abs
    (HarmonicGeneralEndpoint.harmonicBound w s) s (by decide) d m (k+1)
  let f := frame w T s
  let z := (QuadraticSecants.secondState (duration T m) ht (a.approx j) (b.approx j)).1
  have hn : k*blocks j ≤ blocks (m+j) := by
    rw [blocks_add]
    exact Nat.mul_le_mul_right (blocks j) (by omega)
  have ha := node_approx (harmonicOracle w hw) (Fraction.ofInt 1) T (Fraction.ofInt 1) w.abs
    (HarmonicGeneralEndpoint.harmonicBound w s) s (by decide) d m k (by omega) j
  have hp : Fraction.le (pointNorm (a.approx j).1) f.P := by
    rw [ha]
    exact Fraction.magnitudes.le_trans (point_le_state _)
      (HarmonicGeneralTime.actual_run_state_bound w T s hT hs (m+j) (k*blocks j) hn)
  have hv : Fraction.le (pointNorm (a.approx j).2) f.V := by
    rw [ha]
    exact GeneralForcePrefix.count_velocity _ _ _ _ _ _ _ _ d _ _ hn
  have hf : Fraction.le (pointNorm (linearField w (a.approx j).1)) f.A :=
    Fraction.le_equiv_left (HarmonicGeneralEndpoint.linear_sample_norm _ _)
      (Fraction.mul_le_mul_nonnegative_left hp w.abs (Fraction.abs_num_nonnegative w))
  have hb := GeneralForceQuadraticSecants.node_second_sample_bound (harmonicOracle w hw)
    (Fraction.ofInt 1) T (Fraction.ofInt 1) w.abs (HarmonicGeneralEndpoint.harmonicBound w s) s
    (by decide) d ht m k hk j
  have he : Fraction.equiv
      (Fraction.add
        (Fraction.mul (Fraction.ofInt 2) (Fraction.mul w.abs (Fraction.mul (duration T m) f.V)))
        (Fraction.add (Fraction.mul (sampleError (harmonicOracle w hw) (Fraction.ofInt 1) (by decide) (m+j))
            (Fraction.ofInt 2))
          (Fraction.mul (duration (Fraction.ofInt 1) j) (pointNorm (linearField w (a.approx j).1)))))
      (Fraction.add (Fraction.mul (duration T m) f.U)
        (Fraction.mul (duration (Fraction.ofInt 1) j) (pointNorm (linearField w (a.approx j).1)))) := by
    simp only [f,frame,sampleError,harmonicOracle,exactOracle,Fraction.equiv,Fraction.add,
      Fraction.mul,Fraction.ofInt,Int.zero_mul,Int.mul_zero,Int.add_zero,Int.zero_add,
      Int.one_mul,Int.mul_one,Int.add_mul,Int.mul_add]
    ac_nf
  have hd : Fraction.le (pointDistance z (linearField w (a.approx j).1))
      (Fraction.add (Fraction.mul (duration T m) f.U)
        (Fraction.mul (duration (Fraction.ofInt 1) j) f.A)) :=
    Fraction.magnitudes.le_trans (Fraction.le_equiv_right hb he)
      (Fraction.add_le_add_left
        (Fraction.mul_le_mul_nonnegative_left hf (duration (Fraction.ofInt 1) j) (by change (0 : Int)≤1; omega)) _)
  obtain ⟨_,_,hA,hU,_⟩ := frame_nonnegative w T s hT
  have hsmall := duration_le_window T hT m
  have hunit := duration_le_window (Fraction.ofInt 1) (by decide) j
  have hd' : Fraction.le (pointDistance z (linearField w (a.approx j).1))
      (Fraction.add (Fraction.mul T f.U) f.A) := Fraction.magnitudes.le_trans hd (Fraction.add_le_add
    (Fraction.mul_le_mul_nonnegative hsmall f.U hU)
    (Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative hunit f.A hA)
      (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one])))
  have hz := Fraction.magnitudes.le_trans (pointNorm_le_distance_add z (linearField w (a.approx j).1))
    (Fraction.add_le_add hd' hf)
  refine ⟨hp,hv,Fraction.le_equiv_right hz ?_,hd⟩
  simp only [f,frame,Fraction.equiv,Fraction.add,Int.add_mul,Int.mul_add]
  ac_nf

/-- The potential difference is evaluated on the actual constructed endpoint
and the tangent continuation. Its normalized drop has an explicit O(H) bound. -/
theorem normalized_potential_cell_bound (mass w T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (ht : 0 < T.num)
    (m k : Nat) (hk : k+1≤blocks m) :
    Within
      (normalizedStepValue (Fraction.mul mass w).half (duration T m) ht
        (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m k))
        (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m (k+1))))
      (forceEnergyValue mass (HarmonicCompletedForce.linearValue w
        (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m k))))
      (Fraction.mul (duration T m) (coefficient mass w T s)) := by
  let d := HarmonicGeneralTime.conditions w (Fraction.ofInt 1) T s hw (by decide) hT hs
  let a := nodeName (harmonicOracle w hw) (Fraction.ofInt 1) T (Fraction.ofInt 1) w.abs
    (HarmonicGeneralEndpoint.harmonicBound w s) s (by decide) d m k
  let b := nodeName (harmonicOracle w hw) (Fraction.ofInt 1) T (Fraction.ofInt 1) w.abs
    (HarmonicGeneralEndpoint.harmonicBound w s) s (by decide) d m (k+1)
  have hval (i : Nat) : realize (nodeName (harmonicOracle w hw) (Fraction.ofInt 1) T
      (Fraction.ofInt 1) w.abs (HarmonicGeneralEndpoint.harmonicBound w s) s (by decide) d m i) =
      HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m i) := by
    rw [node_value,HarmonicGeneralTime.harmonic_value_eq]
  rw [← hval k,← hval (k+1),← force_work_eq_energy]
  change NameBound (normalizedStepName (Fraction.mul mass w).half (duration T m) ht a b)
    (workName mass w a) _
  let f := frame w T s
  let Q := roundingCoefficient (Fraction.mul mass w).half f.P f.A
  obtain ⟨hP,hV,hA,hU,hZ⟩ := frame_nonnegative w T s hT
  have hQ : 0 ≤ Q.num := Fraction.nonnegative_mul _ _ (Fraction.abs_num_nonnegative _)
    (Fraction.nonnegative_mul _ _ hP hA)
  apply SampledValues.nameBound_of_vanishing_error _ _ _ (fun j => Fraction.mul (duration (Fraction.ofInt 1) j) Q)
  · intro eps heps
    obtain ⟨N,hN⟩ := duration_eventually_small Q eps hQ heps
    refine ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv ?_) (hN j hj)⟩
    simp only [duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
    ac_nf
  · intro j
    obtain ⟨hp,hv,hz,hd⟩ := node_frame_bounds w T s hw hT hs ht m k hk j
    have hb := uniform_frame_bound (Fraction.mul mass w).half (duration T m) T f.P f.V f.Z f.U
      (duration (Fraction.ofInt 1) j) f.A ht (a.approx j) (b.approx j)
      (linearField w (a.approx j).1) hP hV hZ (duration_le_window T hT m) hp hv hz hd
    have he := Fraction.equiv_trans (stateNorm_equiv (HarmonicDyadic.stateSub_congr
      (normalized_step_approximant (Fraction.mul mass w).half (duration T m) ht a b j)
      (work_approximant mass w a j))) (scalarState_distance _ _)
    exact Fraction.le_equiv_left he hb

/-- Uniform leading-order potential drop on all constructed dyadic cells,
including the last cell: Delta V/H² tends to -mass*dot(a_left,a_left)/2. -/
theorem normalized_potential_steps_converge (mass w T : Fraction) (s : Point × Point)
    (hw : 0 ≤ w.num) (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) (ht : 0 < T.num)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m, N≤m → ∀ k, k+1≤blocks m →
      Within
        (normalizedStepValue (Fraction.mul mass w).half (duration T m) ht
          (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m k))
          (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m (k+1))))
        (forceEnergyValue mass (HarmonicCompletedForce.linearValue w
          (HarmonicTimeRealization.gammaValue w T s hT hs (nodeTime T hT m k)))) eps := by
  have hC := coefficient_nonnegative mass w T s hT
  obtain ⟨N,hN⟩ := duration_eventually_small (Fraction.mul T (coefficient mass w T s)) eps
    (Fraction.nonnegative_mul _ _ hT hC) heps
  refine ⟨N,fun m hm k hk => within_mono _ _ _ _ ?_
    (normalized_potential_cell_bound mass w T s hw hT hs ht m k hk)⟩
  apply Fraction.le_equiv_left (b := duration (Fraction.mul T (coefficient mass w T s)) m)
    _ (Fraction.magnitudes.lt_implies_le (hN m hm))
  simp only [duration,Fraction.equiv,Fraction.mul]
  ac_nf

/-- A finite quadratic prediction still has a nonzero potential remainder.
This rational polynomial control is not an independently computed orbit. -/
theorem quadratic_prediction_control :
    let h : Fraction := ⟨1,2,by decide⟩
    let p : Point := (Fraction.ofInt 1,Fraction.ofInt 0)
    let v : Point := (Fraction.ofInt 0,Fraction.ofInt 1)
    let c : Fraction := ⟨1,2,by decide⟩
    let q := QuadraticEstimates.quadraticPosition h (p,v) (linearField (Fraction.ofInt 1) p)
    Fraction.equiv (durationDifference (quadratic c (pointAdd p (pointScale h v))) (quadratic c q))
      (⟨-15,128,by decide⟩ : Fraction) ∧
    ¬ Fraction.equiv (durationDifference (quadratic c (pointAdd p (pointScale h v))) (quadratic c q))
      (⟨-1,8,by decide⟩ : Fraction) := by decide

end NewtonLimitDynamics.Diagnostic.ConstructedHarmonicPotential
