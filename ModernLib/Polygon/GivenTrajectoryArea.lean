import ModernLib.Polygon.GivenMotionComparison
import ModernLib.Polygon.GeneralForceArea

/-! Conditional identification of a supplied motion from its own rational
samples and local mechanical consistency. Existence alone supplies none of
these consistency conditions. Neither polygon agreement nor an area law is
assumed. The sampled consistency conditions are a modern reconstruction,
not a new axiom attributed to Newton. -/
namespace NewtonLimitDynamics.Polygon.GivenTrajectoryArea
open NewtonLimitDynamics
open HarmonicTimeRealization HarmonicBinaryPrefix TimeSubdivision HarmonicDyadic CauchyValues BinaryTime PositionValues
open GeneralForceEndpoint GeneralForcePrefix GeneralForceTime

/-- Rational representations of an independently given state curve. Local
residuals and their scalar accumulation rate are separate mechanical data.
`represents` concerns only the given curve's own samples, not Newton's runs. -/
structure Consistency (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime T d.time_nonnegative → Value) where
  samples : Nat → Nat → Point × Point
  residual : Nat → Fraction
  residual_nonnegative : ∀ j, 0 ≤ (residual j).num
  initial : ∀ j, samples j 0 = s
  arrival_region : ∀ j k, k < blocks j → o.region
    (FiniteEstimates.cell (field o E0 hE j) (duration T j) (samples j k)).1
  local_residual : ∀ j k, k < blocks j → Fraction.le
    (TimeCalibration.distance tau (samples j (k+1))
      (FiniteEstimates.cell (field o E0 hE j) (duration T j) (samples j k)))
    (residual j)
  source_decay : ∀ eps : Fraction, 0 < eps.num → ∃ N, ∀ j, N ≤ j →
    Fraction.le (GivenMotionComparison.errorBudget tau d.calibration_positive
      (duration T j) (sampleError o E0 hE j) (residual j) (blocks j)) eps
  represents : ∀ b : Nat → Bool, ∀ eps : Fraction, 0 < eps.num →
    ∃ N, ∀ j, N ≤ j → Within (embed (samples j (ticks b j))) (u (Quotient.mk _ b)) eps

/-- The independently supplied motion equals the polygon limit as a conclusion
of finite stability and local consistency, not as an existence premise. -/
-- Modern dependency score: 97/268 (M=97, H=171; transitive project theorems/axioms).
theorem equals_constructed (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime T d.time_nonnegative → Value)
    (c : Consistency o E0 T tau L B s hE d u) :
    u = gammaValue o E0 T tau L B s hE d := by
  funext t
  induction t using Quotient.inductionOn with
  | _ b =>
    apply (within_zero_iff _ _).mp
    apply CompletionGeometry.within_of_thickenings
    intro eps heps
    obtain ⟨N,hN⟩ := c.source_decay eps.half.half heps
    obtain ⟨M,hM⟩ := c.represents b eps.half heps
    obtain ⟨P,hP⟩ := prefix_uniform_convergence o E0 T tau L B s hE d
      eps.half.half heps
    let j := N + M + P
    have hNM : N ≤ j := by omega
    have hMM : M ≤ j := by omega
    have hPM : P ≤ j := by omega
    have hf := GivenMotionComparison.count_sample_stateDistance_le_budget
      o E0 T tau L B s hE d j (c.samples j) (c.residual j)
      (c.residual_nonnegative j) (c.initial j) (c.arrival_region j)
      (c.local_residual j) (ticks b j) (ticks_le_blocks b j)
    have hw := (CompletionGeometry.within_embedded_iff _ _ _).mpr
      (Fraction.magnitudes.le_trans hf (hN j hNM))
    have htri := within_triangle _ _ _ _ _
      (within_symm _ _ _ (hM j hMM))
      (within_triangle _ _ _ _ _ (within_symm _ _ _ hw) (hP j hPM b))
    apply within_mono _ _ _ _ (Fraction.le_of_equiv ?_) htri
    exact Fraction.equiv_trans
      (Fraction.add_equiv (Fraction.equiv_refl _) (Fraction.half_add_self eps.half))
      (Fraction.equiv_trans (Fraction.half_add_self eps)
        (Fraction.equiv_symm (by simp [Fraction.equiv,Fraction.add,Fraction.ofInt])))

/-- The given motion has the actual all-interval swept fan law. No area-law
premise is used; the coefficient is its common initial state's momentum. -/
-- Modern dependency score: 164/375 (M=164, H=211; transitive project theorems/axioms).
theorem proportional_swept_area (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime T d.time_nonnegative → Value)
    (c : Consistency o E0 T tau L B s hE d u) :
    SweptArea.Proportional T d.time_nonnegative (fun t => asPosition (u t))
      (CentralSchedule.momentum s) := by
  rw [equals_constructed o E0 T tau L B s hE d u c]
  exact GeneralForceArea.proportional_swept_area o E0 T tau L B s hE d

/-- Separately, the actual matched region has covers whose canonical unsigned
outer contents tend to zero. This is not a subtraction of swept fan areas. -/
-- Modern dependency score: 180/380 (M=180, H=200; transitive project theorems/axioms).
theorem between_path_content_tends_zero (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime T d.time_nonnegative → Value)
    (c : Consistency o E0 T tau L B s hE d u) :
    ∃ covers : ∀ m, SquareOuterContent.Cover
      (MatchedRegion.Region T d.time_nonnegative
        (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m)
        (fun t => asPosition (u t)) m),
      ∀ eps : Fraction, 0 < eps.num → ∃ N, ∀ m, N ≤ m →
        Within (SquareContentValues.contentValue _ (covers m)).val
          (embed (BinaryTime.scalarState (Fraction.ofInt 0))) eps := by
  rw [equals_constructed o E0 T tau L B s hE d u c]
  exact ⟨GeneralForcePathRegion.actualCover o E0 T tau L B s hE d,
    GeneralForcePathContent.D_meshValue_tends_zero o E0 T tau L B s hE d⟩

end NewtonLimitDynamics.Polygon.GivenTrajectoryArea
