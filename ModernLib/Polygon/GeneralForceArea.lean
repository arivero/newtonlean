import ModernLib.Polygon.GeneralForceSecants
import ModernLib.Polygon.GeneralForcePathContent
import ModernLib.Foundation.Polygon.PairingValues
import ModernLib.Foundation.Polygon.FanValues
import ModernLib.Foundation.Polygon.GeometricApproximation
import ModernLib.Foundation.Polygon.SweptArea

/-! Swept area of the actual constructed local central-force curve.
The model is planar by definition. All regularity, finite-force and calibrated
window assumptions remain explicit modern reconstruction premises. -/

namespace NewtonLimitDynamics.Polygon.GeneralForceArea
open NewtonLimitDynamics
open TimeSubdivision PointBounds ForceClasses HarmonicDyadic HarmonicBinaryPrefix
open CauchyValues BinaryTime PositionValues SecantValues PairingValues DyadicNodes HarmonicTimeRealization SweptArea
open GeneralForceEndpoint GeneralForcePrefix GeneralForceTime GeneralForceSecants

-- Modern dependency score: 5/26 (M=5, H=21; transitive project theorems/axioms).
theorem count_areal_product (o : CentralOracle) (E0 T : Fraction)
    (s : Point × Point) (hE : 0 < E0.num) (j n : Nat) :
    Fraction.equiv (CentralSchedule.momentum (countState o E0 T s hE j n))
      (CentralSchedule.momentum s) := by
  rw [GeneralForcePrefix.countState,run_eq_schedule]
  exact CentralSchedule.schedule_momentum _ (sample_central o _) _ s

/-- Supporting differential content. This is not the swept-area theorem:
the determinant of the constructed position and its identified velocity is
constant because every actual finite prefix has that determinant. -/
-- Modern dependency score: 79/256 (M=79, H=177; transitive project theorems/axioms).
theorem areal_product_value (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime T d.time_nonnegative) :
    pairingValue detForm (gammaValue o E0 T tau L B s hE d t)
      (velocityValue (gammaValue o E0 T tau L B s hE d t)) =
      embed (scalarState (CentralSchedule.momentum s)) := by
  induction t using Quotient.inductionOn with
  | _ b =>
    apply Quotient.sound
    apply nameEquiv_of_levelwise_stateEquiv
    intro j
    change stateEquiv (scalarState (CentralSchedule.momentum (prefixState b o E0 T s hE j)))
      (scalarState (CentralSchedule.momentum s))
    exact ⟨⟨count_areal_product o E0 T s hE j (ticks b j),Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩

/-- A determinant triangle uses two actual curve-node approximants. The
restarted finite drift remainder gives its quadratic error, uniformly in the
approximant index. It is not a triangle of an assumed trajectory. -/
-- Modern dependency score: 57/225 (M=57, H=168; transitive project theorems/axioms).
theorem node_triangle_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (m k j : Nat) (hk : k+1≤blocks m) :
    Fraction.le
      (HarmonicTimeComparison.durationDifference
        (Fraction.mul (duration T m) (CentralSchedule.momentum s))
        (TimeSubdivision.det ((nodeName o E0 T tau L B s hE d m k).approx j).1
          ((nodeName o E0 T tau L B s hE d m (k+1)).approx j).1)).abs
      (Fraction.mul d.outer_radius (Fraction.mul (Fraction.mul (duration T m) (duration T m)) B)) := by
  rw [node_approx o E0 T tau L B s hE d m k (by omega) j,
    node_approx o E0 T tau L B s hE d m (k+1) hk j]
  let a := field o E0 hE (m+j)
  let h := duration T (m+j)
  let n := k*blocks j
  let q := GeneralForcePrefix.countState o E0 T s hE (m+j) n
  let u := BoundedIteration.time h (blocks j)
  have hn : n+blocks j ≤ blocks (m+j) := by
    rw [blocks_add]
    have hm := Nat.mul_le_mul_right (blocks j) hk
    simpa only [n,Nat.add_mul,Nat.one_mul] using hm
  have hb := BoundedIteration.boundedSamples_restart a h s B (blocks (m+j)) n (blocks j)
    hn (d.actual_samples (m+j))
  have hr := KinematicEstimates.position_remainder a h q B d.time_nonnegative d.bound_nonnegative (blocks j) hb
  have hp : Fraction.le (pointNorm q.1) d.outer_radius :=
    (d.toConditions.run_band (m+j) h d.time_nonnegative n
      (count_time_le T d.time_nonnegative (m+j) n (by omega))).2
  have he : Fraction.equiv u (duration T m) := grid_time T m j
  have hm := count_areal_product o E0 T s hE (m+j) n
  have ha := PolygonFanArea.det_inertial_remainder_bound q.1 q.2
    (BoundedIteration.run a h q (blocks j)).1 u d.outer_radius
    (Fraction.mul (Fraction.mul u u) B) hp hr
  have hleft := HarmonicTimeComparison.difference_congr
    (Fraction.mul_equiv (Fraction.equiv_symm he) (Fraction.equiv_symm hm))
    (Fraction.equiv_refl (TimeSubdivision.det q.1 (BoundedIteration.run a h q (blocks j)).1))
  have hright := Fraction.mul_equiv (Fraction.equiv_refl d.outer_radius)
    (Fraction.mul_equiv (Fraction.mul_equiv he he) (Fraction.equiv_refl B))
  have hbound := Fraction.le_equiv_right
    (Fraction.le_equiv_left (Fraction.abs_equiv hleft) ha) hright
  change Fraction.le (HarmonicTimeComparison.durationDifference _
    (TimeSubdivision.det (BoundedIteration.run a h s n).1
      (BoundedIteration.run a h (BoundedIteration.run a h s n) (blocks j)).1)).abs _ at hbound
  rw [← BoundedIteration.run_add] at hbound
  have hecount : n+blocks j=(k+1)*blocks j := by simp only [n,Nat.add_mul,Nat.one_mul]
  rw [hecount] at hbound
  exact hbound

def areaMomentum (unsigned : Bool) (s : Point × Point) : Fraction :=
  if unsigned then (CentralSchedule.momentum s).abs else CentralSchedule.momentum s

noncomputable def curveFanName (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m n : Nat) : EndpointCauchyName :=
  FanValues.fanName unsigned (nodeName o E0 T tau L B s hE d m) n

/-- A doubled triangle fan built from actual points of the constructed curve.
The right boundary is included when n=2^m. -/
noncomputable def curveFanValue (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m n : Nat) : Value :=
  FanValues.fanValue unsigned
    (fun k => gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k)) n

-- Modern dependency score: 90/262 (M=90, H=172; transitive project theorems/axioms).
theorem curveFanValue_realize (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m n : Nat) :
    curveFanValue unsigned o E0 T tau L B s hE d m n =
      realize (curveFanName unsigned o E0 T tau L B s hE d m n) := by
  unfold curveFanValue
  rw [← funext (node_value o E0 T tau L B s hE d m)]
  exact FanValues.fanValue_realize unsigned _ n

/-- Unsigned and oriented fans share the same cell-error proof. Absolute
values are taken cell by cell, so opposite lobes cannot cancel in the former. -/
-- Modern dependency score: 74/261 (M=74, H=187; transitive project theorems/axioms).
theorem fan_approximant_bound (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m n j : Nat) (hn : n≤blocks m) :
    Fraction.le
      (distance ((curveFanName unsigned o E0 T tau L B s hE d m n).approx j)
        (scalarState (Fraction.mul (countTime T m n) (areaMomentum unsigned s))))
      (Fraction.mul (Fraction.ofInt (n : Int))
        (Fraction.mul d.outer_radius (Fraction.mul (Fraction.mul (duration T m) (duration T m)) B))) := by
  rw [curveFanName,FanValues.fanName_approx]
  apply Fraction.le_equiv_left (scalarState_distance _ _)
  let c := Fraction.mul (duration T m) (areaMomentum unsigned s)
  let p := fun i => ((nodeName o E0 T tau L B s hE d m i).approx j).1
  let terms := fun i => if unsigned then (TimeSubdivision.det (p i) (p (i+1))).abs
    else TimeSubdivision.det (p i) (p (i+1))
  have hterms : ∀ i, i<n → Fraction.le (PolygonFanArea.sub (terms i) c).abs
      (Fraction.mul d.outer_radius (Fraction.mul (Fraction.mul (duration T m) (duration T m)) B)) := by
    intro i hi
    have hb := node_triangle_bound o E0 T tau L B s hE d m i j (by omega)
    cases unsigned with
    | false => exact hb
    | true =>
      have he : Fraction.equiv
          (Fraction.mul (duration T m) (CentralSchedule.momentum s)).abs c :=
        Fraction.equiv_trans (Fraction.abs_mul _ _)
          (Fraction.mul_equiv (Fraction.abs_of_nonnegative _ d.time_nonnegative) (Fraction.equiv_refl _))
      exact Fraction.le_equiv_left
        (Fraction.abs_equiv (HarmonicTimeComparison.difference_congr (Fraction.equiv_symm he) (Fraction.equiv_refl _)))
        (Fraction.magnitudes.le_trans (PolygonFanArea.duration_abs_reverse _ _) hb)
  have hs := PolygonFanArea.sum_error terms (fun _ => c) _ n hterms
  have hc : Fraction.equiv (PolygonFanArea.sum (fun _ => c) n)
      (Fraction.mul (countTime T m n) (areaMomentum unsigned s)) :=
    Fraction.equiv_trans (PolygonFanArea.sum_constant c n)
      (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))
  have hf : FanValues.finiteFan unsigned p n = PolygonFanArea.sum terms n := by
    cases unsigned <;> rfl
  rw [hf]
  exact Fraction.le_equiv_left
    (Fraction.abs_equiv (HarmonicTimeComparison.difference_congr (Fraction.equiv_symm hc) (Fraction.equiv_refl _))) hs

noncomputable def curveIntervalName (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (b c : Nat → Bool) (m : Nat) : EndpointCauchyName :=
  FanValues.intervalName true (nodeName o E0 T tau L B s hE d m)
    (intervalStart b c m) (intervalCount b c m)

noncomputable def curveIntervalValue (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (b c : Nat → Bool) (m : Nat) : Value :=
  FanValues.intervalValue true
    (fun k => gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k))
    (intervalStart b c m) (intervalCount b c m)

-- Modern dependency score: 91/263 (M=91, H=172; transitive project theorems/axioms).
theorem curveIntervalValue_realize (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (b c : Nat → Bool) (m : Nat) :
    curveIntervalValue o E0 T tau L B s hE d b c m =
      realize (curveIntervalName o E0 T tau L B s hE d b c m) := by
  unfold curveIntervalValue curveIntervalName
  rw [← funext (node_value o E0 T tau L B s hE d m)]
  exact FanValues.intervalValue_realize true _ _ _

-- Modern dependency score: 76/264 (M=76, H=188; transitive project theorems/axioms).
theorem interval_fan_approximant_bound (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (b c : Nat → Bool) (m j : Nat) :
    Fraction.le
      (distance ((curveIntervalName o E0 T tau L B s hE d b c m).approx j)
        (scalarState (Fraction.mul (countTime T m (intervalCount b c m))
          (areaMomentum true s))))
      (Fraction.mul (Fraction.ofInt (intervalCount b c m : Int))
        (Fraction.mul d.outer_radius (Fraction.mul (Fraction.mul (duration T m) (duration T m)) B))) := by
  rw [curveIntervalName,FanValues.intervalName_approx]
  apply Fraction.le_equiv_left (scalarState_distance _ _)
  let lo := intervalStart b c m
  let n := intervalCount b c m
  let e := Fraction.mul d.outer_radius (Fraction.mul (Fraction.mul (duration T m) (duration T m)) B)
  let c₀ := Fraction.mul (duration T m) (areaMomentum true s)
  let p := fun i => ((nodeName o E0 T tau L B s hE d m i).approx j).1
  let terms := fun i => (TimeSubdivision.det (p i) (p (i+1))).abs
  have hterms : ∀ i, i<n → Fraction.le (PolygonFanArea.sub (terms (lo+i)) c₀).abs e := by
    intro i hi
    have hb := node_triangle_bound o E0 T tau L B s hE d m (lo+i) j
      (by have he := interval_end_le_blocks b c m; dsimp [lo,n] at *; omega)
    have he : Fraction.equiv
        (Fraction.mul (duration T m) (CentralSchedule.momentum s)).abs c₀ :=
      Fraction.equiv_trans (Fraction.abs_mul _ _)
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative _ d.time_nonnegative) (Fraction.equiv_refl _))
    exact Fraction.le_equiv_left
      (Fraction.abs_equiv (HarmonicTimeComparison.difference_congr (Fraction.equiv_symm he) (Fraction.equiv_refl _)))
      (Fraction.magnitudes.le_trans (PolygonFanArea.duration_abs_reverse _ _) hb)
  have hs := PolygonFanArea.intervalSum_error terms (fun _ => c₀) lo n e hterms
  have hc : Fraction.equiv (PolygonFanArea.intervalSum (fun _ => c₀) lo n)
      (Fraction.mul (countTime T m n) (areaMomentum true s)) :=
    Fraction.equiv_trans (PolygonFanArea.sum_constant c₀ n)
      (Fraction.equiv_symm (Fraction.mul_assoc _ _ _))
  change Fraction.le (HarmonicTimeComparison.durationDifference _ _).abs _
  exact Fraction.le_equiv_left
    (Fraction.abs_equiv (HarmonicTimeComparison.difference_congr
      (Fraction.equiv_symm hc) (Fraction.equiv_refl _))) hs

def intervalReferenceName (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (s : Point × Point) : EndpointCauchyName :=
  secantName (areaMomentum true s).half (intervalElapsedName b c T hT)
    (constantName FanValues.zeroState)

-- Modern dependency score: 21/107 (M=21, H=86; transitive project theorems/axioms).
theorem interval_reference_approx (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (s : Point × Point) (m : Nat) :
    stateEquiv ((intervalReferenceName b c T hT s).approx m)
      (FanValues.halfState (scalarState
        (Fraction.mul (countTime T m (intervalCount b c m)) (areaMomentum true s)))) := by
  have he := interval_elapsed_approx b c T hT m
  have hs : stateEquiv ((intervalReferenceName b c T hT s).approx m)
      (secantState (areaMomentum true s).half
        (scalarState (countTime T m (intervalCount b c m))) FanValues.zeroState) := by
    exact ⟨pointScale_congr _
      (pointSub_congr he.1 ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩),
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩
  have hp := FanValues.half_scalar_product (areaMomentum true s)
    (countTime T m (intervalCount b c m))
  exact ⟨pointEquiv_trans hs.1 (pointEquiv_symm hp.1),
    pointEquiv_trans hs.2 (pointEquiv_symm hp.2)⟩

-- Modern dependency score: 1/6 (M=1, H=5; transitive project theorems/axioms).
theorem outer_radius_nonnegative (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) : 0 ≤ d.outer_radius.num :=
  Fraction.nonnegative_of_le (Fraction.nonnegative_add _ _ (pointNorm_nonnegative _)
    (Fraction.nonnegative_mul _ _ d.time_nonnegative
      (velocityCap_nonnegative T B s d.time_nonnegative d.bound_nonnegative))) d.frame.outer_bound

def fanErrorCoefficient (T B R : Fraction) : Fraction :=
  Fraction.mul R (Fraction.mul (Fraction.mul T T) B)

-- Modern dependency score: 0/1 (M=0, H=1; transitive project theorems/axioms).
theorem fanErrorCoefficient_nonnegative (T B R : Fraction)
    (hT : 0 ≤ T.num) (hB : 0 ≤ B.num) (hR : 0 ≤ R.num) :
    0 ≤ (fanErrorCoefficient T B R).num :=
  Fraction.nonnegative_mul _ _ hR
    (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hT hT) hB)

/-- Uniform geometric decay for a fan on actual curve nodes. No curve-area
law or convergence premise is supplied. The sum has at most 2^m cells. -/
-- Modern dependency score: 77/265 (M=77, H=188; transitive project theorems/axioms).
theorem fan_approximant_geometric (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m n j : Nat) (hn : n≤blocks m) :
    Fraction.le
      (distance ((curveFanName unsigned o E0 T tau L B s hE d m n).approx j)
        (scalarState (Fraction.mul (countTime T m n) (areaMomentum unsigned s))))
      (duration (fanErrorCoefficient T B d.outer_radius) m) := by
  have hr := outer_radius_nonnegative o E0 T tau L B s hE d
  let e := Fraction.mul d.outer_radius (Fraction.mul (Fraction.mul (duration T m) (duration T m)) B)
  have he : 0 ≤ e.num := fanErrorCoefficient_nonnegative (duration T m) B d.outer_radius
    d.time_nonnegative d.bound_nonnegative hr
  have hcount : Fraction.le (Fraction.ofInt (n : Int)) (Fraction.ofInt (blocks m : Int)) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one] using Int.ofNat_le.mpr hn
  have hb := Fraction.magnitudes.le_trans
    (fan_approximant_bound unsigned o E0 T tau L B s hE d m n j hn)
    (Fraction.mul_le_mul_nonnegative hcount e he)
  apply Fraction.le_equiv_right hb
  simp only [e,fanErrorCoefficient,duration,blocks,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_pow]
  ac_nf

-- Modern dependency score: 118/314 (M=118, H=196; transitive project theorems/axioms).
theorem curve_fan_polygon_bound (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m n : Nat) (hn : n≤blocks m) :
    Within (curveFanValue unsigned o E0 T tau L B s hE d m n)
      (embed (scalarState (Fraction.mul (countTime T m n) (areaMomentum unsigned s))))
      (duration (fanErrorCoefficient T B d.outer_radius) m) := by
  rw [curveFanValue_realize]
  exact nameBound_of_eventual_le _ _ _ 0
    (fun j _ => fan_approximant_geometric unsigned o E0 T tau L B s hE d m n j hn)

def areaReferenceName (unsigned : Bool) (b : Nat → Bool) (T : Fraction)
    (hT : 0 ≤ T.num) (s : Point × Point) : EndpointCauchyName :=
  secantName (areaMomentum unsigned s).half (BinaryTime.timeName b T hT)
    (constantName FanValues.zeroState)

/-- The fan's completed half-area is close to its level-m polygon area.
This estimate uses genuine curve-node fan approximants for every j. -/
-- Modern dependency score: 87/283 (M=87, H=196; transitive project theorems/axioms).
theorem area_fan_reference_bound (unsigned : Bool) (b : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m j : Nat) :
    Fraction.le
      (distance (FanValues.halfState ((curveFanName unsigned o E0 T tau L B s hE d m (ticks b m)).approx j))
        ((areaReferenceName unsigned b T d.time_nonnegative s).approx m))
      (duration (fanErrorCoefficient T B d.outer_radius) m) := by
  have hb := Fraction.magnitudes.le_trans (FanValues.half_nonexpansive _ _)
    (fan_approximant_geometric unsigned o E0 T tau L B s hE d m (ticks b m) j (ticks_le_blocks b m))
  have hp := FanValues.half_scalar_product (areaMomentum unsigned s) (timeApprox b T m)
  have hd := stateNorm_equiv (stateSub_congr
    (show stateEquiv
      (FanValues.halfState ((curveFanName unsigned o E0 T tau L B s hE d m (ticks b m)).approx j))
      (FanValues.halfState ((curveFanName unsigned o E0 T tau L B s hE d m (ticks b m)).approx j))
      from ⟨⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩)
    ⟨pointEquiv_symm hp.1,pointEquiv_symm hp.2⟩)
  exact Fraction.le_equiv_left hd hb

-- Modern dependency score: 79/268 (M=79, H=189; transitive project theorems/axioms).
theorem interval_fan_approximant_geometric (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (b c : Nat → Bool) (m j : Nat) :
    Fraction.le
      (distance ((curveIntervalName o E0 T tau L B s hE d b c m).approx j)
        (scalarState (Fraction.mul (countTime T m (intervalCount b c m))
          (areaMomentum true s))))
      (duration (fanErrorCoefficient T B d.outer_radius) m) := by
  have hr := outer_radius_nonnegative o E0 T tau L B s hE d
  let e := Fraction.mul d.outer_radius (Fraction.mul (Fraction.mul (duration T m) (duration T m)) B)
  have he : 0 ≤ e.num := fanErrorCoefficient_nonnegative (duration T m) B d.outer_radius
    d.time_nonnegative d.bound_nonnegative hr
  have hn : intervalCount b c m ≤ blocks m := by
    have h := interval_end_le_blocks b c m
    omega
  have hcount : Fraction.le (Fraction.ofInt (intervalCount b c m : Int))
      (Fraction.ofInt (blocks m : Int)) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one] using Int.ofNat_le.mpr hn
  have hb := Fraction.magnitudes.le_trans
    (interval_fan_approximant_bound o E0 T tau L B s hE d b c m j)
    (Fraction.mul_le_mul_nonnegative hcount e he)
  apply Fraction.le_equiv_right hb
  simp only [e,fanErrorCoefficient,duration,blocks,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.natCast_pow]
  ac_nf

-- Modern dependency score: 92/294 (M=92, H=202; transitive project theorems/axioms).
theorem interval_fan_reference_bound (b c : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) (m j : Nat) :
    Fraction.le
      (distance (FanValues.halfState
        ((curveIntervalName o E0 T tau L B s hE d b c m).approx j))
        ((intervalReferenceName b c T d.time_nonnegative s).approx m))
      (duration (fanErrorCoefficient T B d.outer_radius) m) := by
  have hb := Fraction.magnitudes.le_trans (FanValues.half_nonexpansive _ _)
    (interval_fan_approximant_geometric o E0 T tau L B s hE d b c m j)
  have hp := interval_reference_approx b c T d.time_nonnegative s m
  have hd := stateNorm_equiv (stateSub_congr
    (show stateEquiv
      (FanValues.halfState ((curveIntervalName o E0 T tau L B s hE d b c m).approx j))
      (FanValues.halfState ((curveIntervalName o E0 T tau L B s hE d b c m).approx j))
      from ⟨⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩)
    ⟨pointEquiv_symm hp.1,pointEquiv_symm hp.2⟩)
  exact Fraction.le_equiv_left (Fraction.equiv_symm hd) hb

/-- The diagonal approximants are the half-fans of actual curve nodes. -/
noncomputable def intervalName (b c : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) : EndpointCauchyName :=
  GeometricApproximation.name (intervalReferenceName b c T d.time_nonnegative s)
    (fun m => FanValues.halfState
      ((curveIntervalName o E0 T tau L B s hE d b c m).approx m))
    (fanErrorCoefficient T B d.outer_radius)
    (fanErrorCoefficient_nonnegative T B d.outer_radius d.time_nonnegative d.bound_nonnegative
      (outer_radius_nonnegative o E0 T tau L B s hE d))
    (fun m => interval_fan_reference_bound b c o E0 T tau L B s hE d m m)

-- Modern dependency score: 95/299 (M=95, H=204; transitive project theorems/axioms).
theorem intervalName_equiv_reference (b c : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    NameEquiv (intervalName b c o E0 T tau L B s hE d)
      (intervalReferenceName b c T d.time_nonnegative s) :=
  GeometricApproximation.name_equiv _ _ _ _ _

-- Modern dependency score: 104/308 (M=104, H=204; transitive project theorems/axioms).
theorem intervalName_address_equiv (b c b' c' : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (hb : AddressEquiv T d.time_nonnegative b b')
    (hc : AddressEquiv T d.time_nonnegative c c') :
    NameEquiv (intervalName b c o E0 T tau L B s hE d)
      (intervalName b' c' o E0 T tau L B s hE d) := by
  have he : NameEquiv (intervalElapsedName b c T d.time_nonnegative)
      (intervalElapsedName b' c' T d.time_nonnegative) :=
    mapName_equiv FanValues.absoluteState FanValues.absolute_nonexpansive
      (secantName_equiv (Fraction.ofInt 1) _ _ _ _ hb hc)
  have hr := secantName_equiv (areaMomentum true s).half _ _ _ _ he
    (nameEquiv_refl (constantName FanValues.zeroState))
  exact nameEquiv_trans (intervalName_equiv_reference b c o E0 T tau L B s hE d)
    (nameEquiv_trans hr
      (nameEquiv_symm (intervalName_equiv_reference b' c' o E0 T tau L B s hE d)))

/-- Actual interval-fan approximants construct the area. Their address
independence is established before this two-endpoint quotient lift. -/
noncomputable def intervalAreaValue (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime T d.time_nonnegative) : Value :=
  Quotient.liftOn₂ t₀ t₁
    (fun b c => realize (intervalName b c o E0 T tau L B s hE d))
    (fun b c b' c' hb hc => Quotient.sound
      (intervalName_address_equiv b c b' c' o E0 T tau L B s hE d hb hc))

-- Modern dependency score: 108/312 (M=108, H=204; transitive project theorems/axioms).
theorem intervalAreaValue_reference (b c : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    intervalAreaValue o E0 T tau L B s hE d (Quotient.mk _ b) (Quotient.mk _ c) =
      realize (intervalReferenceName b c T d.time_nonnegative s) :=
  Quotient.sound (intervalName_equiv_reference b c o E0 T tau L B s hE d)

/-- The elapsed-time formula is a consequence of the actual fan construction. -/
-- Modern dependency score: 109/313 (M=109, H=204; transitive project theorems/axioms).
theorem interval_area_time_formula (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime T d.time_nonnegative) :
    intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      secantValue (CentralSchedule.momentum s).abs.half
        (intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (embed FanValues.zeroState) := by
  induction t₀ using Quotient.inductionOn with
  | _ b =>
    induction t₁ using Quotient.inductionOn with
    | _ c => exact intervalAreaValue_reference b c o E0 T tau L B s hE d

/-- The unsigned fan on the actual curve-node interval converges to the
absolute elapsed-time area. Both addresses are quantified in `AreaBetween`. -/
-- Modern dependency score: 147/353 (M=147, H=206; transitive project theorems/axioms).
theorem interval_area_is_swept (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (intervalAreaValue o E0 T tau L B s hE d t₀ t₁) := by
  intro b c hb hc eps heps
  subst t₀
  subst t₁
  rw [intervalAreaValue_reference]
  let C := fanErrorCoefficient T B d.outer_radius
  have hC := fanErrorCoefficient_nonnegative T B d.outer_radius
    d.time_nonnegative d.bound_nonnegative
    (outer_radius_nonnegative o E0 T tau L B s hE d)
  obtain ⟨N,hN⟩ := duration_eventually_small C eps.half hC heps
  obtain ⟨M,hM⟩ := constant_approximants_converge
    (intervalReferenceName b c T d.time_nonnegative s) eps.half heps
  refine ⟨max N M,fun m hm => ?_⟩
  have hf : Within (FanValues.halfValue
      (curveIntervalValue o E0 T tau L B s hE d b c m))
      (embed ((intervalReferenceName b c T d.time_nonnegative s).approx m))
      (duration C m) := by
    rw [curveIntervalValue_realize,FanValues.halfValue_realize]
    exact nameBound_of_eventual_le _ _ _ 0
      (fun j _ => interval_fan_reference_bound b c o E0 T tau L B s hE d m j)
  have hs := within_mono _ _ _ _ (Fraction.magnitudes.lt_implies_le (hN m (by omega))) hf
  have ht := within_mono _ _ _ _ (Fraction.le_of_equiv (Fraction.half_add_self eps))
    (within_triangle _ _ _ _ _ hs (hM m (by omega)))
  change Within (FanValues.halfValue (FanValues.intervalValue true
    (fun k => positionValue (gammaValue o E0 T tau L B s hE d
      (nodeTime T d.time_nonnegative m k)))
    (intervalStart b c m) (intervalCount b c m))) _ eps
  rw [FanValues.intervalValue_positions]
  exact ht

-- Modern dependency score: 152/358 (M=152, H=206; transitive project theorems/axioms).
theorem interval_area_reverse (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime T d.time_nonnegative) :
    intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      intervalAreaValue o E0 T tau L B s hE d t₁ t₀ :=
  SweptArea.areaBetween_unique T d.time_nonnegative _ _ _ _ _
    (interval_area_is_swept o E0 T tau L B s hE d t₀ t₁)
    (SweptArea.areaBetween_reverse T d.time_nonnegative _ _ _ _
      (interval_area_is_swept o E0 T tau L B s hE d t₁ t₀))

-- Modern dependency score: 110/314 (M=110, H=204; transitive project theorems/axioms).
theorem interval_areas_equal_of_equal_elapsed (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ u₀ u₁ : BinaryTime T d.time_nonnegative)
    (h : intervalElapsedValue T d.time_nonnegative t₀ t₁ =
      intervalElapsedValue T d.time_nonnegative u₀ u₁) :
    intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      intervalAreaValue o E0 T tau L B s hE d u₀ u₁ := by
  rw [interval_area_time_formula o E0 T tau L B s hE d t₀ t₁,
    interval_area_time_formula o E0 T tau L B s hE d u₀ u₁,h]

/-- A zero-length interval is empty even when the time has several addresses. -/
-- Modern dependency score: 109/313 (M=109, H=204; transitive project theorems/axioms).
theorem interval_area_zero (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime T d.time_nonnegative) :
    intervalAreaValue o E0 T tau L B s hE d t t = embed FanValues.zeroState := by
  induction t using Quotient.inductionOn with
  | _ b =>
    apply Quotient.sound
    apply nameEquiv_of_levelwise_stateEquiv
    intro m
    change stateEquiv
      (FanValues.halfState
        ((FanValues.intervalName true (nodeName o E0 T tau L B s hE d m)
          (intervalStart b b m) (intervalCount b b m)).approx m)) FanValues.zeroState
    simp only [intervalCount,intervalStart,Nat.max_self,Nat.min_self,Nat.sub_self,
      FanValues.intervalName,FanValues.fanName,FanValues.sumNames,constantName]
    change stateEquiv (FanValues.halfState FanValues.zeroState) FanValues.zeroState
    decide

/-- Actual inscribed triangle fan approximants, on progressively finer grids.
The reference proves their Cauchy property; it is not their definition. -/
noncomputable def sectorName (unsigned : Bool) (b : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) : EndpointCauchyName :=
  GeometricApproximation.name (areaReferenceName unsigned b T d.time_nonnegative s)
    (fun m => FanValues.halfState ((curveFanName unsigned o E0 T tau L B s hE d m (ticks b m)).approx m))
    (fanErrorCoefficient T B d.outer_radius)
    (fanErrorCoefficient_nonnegative T B d.outer_radius d.time_nonnegative d.bound_nonnegative
      (outer_radius_nonnegative o E0 T tau L B s hE d))
    (fun m => area_fan_reference_bound unsigned b o E0 T tau L B s hE d m m)

-- Modern dependency score: 90/288 (M=90, H=198; transitive project theorems/axioms).
theorem sectorName_equiv_reference (unsigned : Bool) (b : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    NameEquiv (sectorName unsigned b o E0 T tau L B s hE d)
      (areaReferenceName unsigned b T d.time_nonnegative s) :=
  GeometricApproximation.name_equiv _ _ _ _ _

-- Modern dependency score: 98/296 (M=98, H=198; transitive project theorems/axioms).
theorem sectorName_address_equiv (unsigned : Bool) (b c : Nat → Bool) (o : CentralOracle)
    (E0 T tau L B : Fraction) (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (hbc : AddressEquiv T d.time_nonnegative b c) :
    NameEquiv (sectorName unsigned b o E0 T tau L B s hE d)
      (sectorName unsigned c o E0 T tau L B s hE d) :=
  nameEquiv_trans (sectorName_equiv_reference unsigned b o E0 T tau L B s hE d)
    (nameEquiv_trans (secantName_equiv _ _ _ _ _ hbc (nameEquiv_refl _))
      (nameEquiv_symm (sectorName_equiv_reference unsigned c o E0 T tau L B s hE d)))

/-- Swept sector area constructed from triangle fans of the actual curve.
Unsigned fans count swept triangles with multiplicity, including repeated
revolutions. Oriented fans retain the orientation. This is not union content. -/
noncomputable def sectorAreaValue (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime T d.time_nonnegative) : Value :=
  Quotient.liftOn t (fun b => realize (sectorName unsigned b o E0 T tau L B s hE d))
    (fun b c hbc => Quotient.sound (sectorName_address_equiv unsigned b c o E0 T tau L B s hE d hbc))

/-- The area law, in the constructed time/value spaces: area = ell*t/2 for
oriented area and |ell|*t/2 for unsigned swept area. No area limit premise. -/
-- Modern dependency score: 102/300 (M=102, H=198; transitive project theorems/axioms).
theorem sector_area_time_formula (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime T d.time_nonnegative) :
    sectorAreaValue unsigned o E0 T tau L B s hE d t =
      secantValue (areaMomentum unsigned s).half
        (timeCoordinate T d.time_nonnegative t) (embed FanValues.zeroState) := by
  induction t using Quotient.inductionOn with
  | _ b => exact Quotient.sound (sectorName_equiv_reference unsigned b o E0 T tau L B s hE d)

/-- This is the geometric identification: the constructed area is the limit
of triangle fans whose vertices lie on the actual constructed position map.
No polygon-sector enclosure or assumed area-convergence premise occurs. -/
-- Modern dependency score: 139/342 (M=139, H=203; transitive project theorems/axioms).
theorem sector_area_is_swept (unsigned : Bool) (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt unsigned T d.time_nonnegative (gammaPosition o E0 T tau L B s hE d) t
      (sectorAreaValue unsigned o E0 T tau L B s hE d t) := by
  intro b hbt eps heps
  subst t
  have harea : sectorAreaValue unsigned o E0 T tau L B s hE d (Quotient.mk _ b) =
      realize (areaReferenceName unsigned b T d.time_nonnegative s) :=
    Quotient.sound (sectorName_equiv_reference unsigned b o E0 T tau L B s hE d)
  rw [harea]
  let C := fanErrorCoefficient T B d.outer_radius
  have hC := fanErrorCoefficient_nonnegative T B d.outer_radius d.time_nonnegative d.bound_nonnegative
    (outer_radius_nonnegative o E0 T tau L B s hE d)
  obtain ⟨N,hN⟩ := duration_eventually_small C eps.half hC heps
  obtain ⟨M,hM⟩ := constant_approximants_converge
    (areaReferenceName unsigned b T d.time_nonnegative s) eps.half heps
  refine ⟨max N M,fun m hm => ?_⟩
  have hf : Within (FanValues.halfValue (curveFanValue unsigned o E0 T tau L B s hE d m (ticks b m)))
      (embed ((areaReferenceName unsigned b T d.time_nonnegative s).approx m)) (duration C m) := by
    rw [curveFanValue_realize,FanValues.halfValue_realize]
    exact nameBound_of_eventual_le _ _ _ 0
      (fun j _ => area_fan_reference_bound unsigned b o E0 T tau L B s hE d m j)
  have hs := within_mono _ _ _ _ (Fraction.magnitudes.lt_implies_le (hN m (by omega))) hf
  have ht := within_mono _ _ _ _ (Fraction.le_of_equiv (Fraction.half_add_self eps))
    (within_triangle _ _ _ _ _ hs (hM m (by omega)))
  change Within (FanValues.halfValue (FanValues.fanValue unsigned
    (fun k => positionValue (gammaValue o E0 T tau L B s hE d (nodeTime T d.time_nonnegative m k)))
    (ticks b m))) _ eps
  rw [FanValues.fanValue_positions]
  exact ht

/-- General local Proposition I reconstruction: the actual position curve
has unsigned swept area proportional to time, and its actual intervening
polygon-region content vanishes. The area coefficient and enclosure are
derived, not premises. Regularity/window data remain modern premises. -/
-- Modern dependency score: 234/459 (M=234, H=225; transitive project theorems/axioms).
theorem constructed_area_law (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative (gammaPosition o E0 T tau L B s hE d) t
      (sectorAreaValue true o E0 T tau L B s hE d t) ∧
    sectorAreaValue true o E0 T tau L B s hE d t =
      secantValue (CentralSchedule.momentum s).abs.half
        (timeCoordinate T d.time_nonnegative t) (embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  ⟨sector_area_is_swept true o E0 T tau L B s hE d t,
    sector_area_time_formula true o E0 T tau L B s hE d t,
    GeneralForcePathContent.polygon_trajectory_defect_vanishes o E0 T tau L B s hE d⟩

/-- Unsigned swept area on any interval of the actual local curve, with its
derived elapsed-time formula and the existing intervening-content exhaustion.
This is a modern regional reconstruction; the historical invoked corollaries
remain separate proof obligations. -/
-- Modern dependency score: 242/469 (M=242, H=227; transitive project theorems/axioms).
theorem constructed_interval_area_law (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      secantValue (CentralSchedule.momentum s).abs.half
        (intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  ⟨interval_area_is_swept o E0 T tau L B s hE d t₀ t₁,
    interval_area_time_formula o E0 T tau L B s hE d t₀ t₁,
    GeneralForcePathContent.polygon_trajectory_defect_vanishes o E0 T tau L B s hE d⟩

/-- The retained constructive development supplies one proved instance of
the given-trajectory swept-area target. Construction is supporting work;
`SweptArea.Proportional` itself requires only an existing curve as data.
The between-path content theorem is separate and is not a field of this law. -/
-- Modern dependency score: 149/355 (M=149, H=206; transitive project theorems/axioms).
theorem proportional_swept_area (o : CentralOracle) (E0 T tau L B : Fraction)
    (s : Point × Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    SweptArea.Proportional T d.time_nonnegative
      (gammaPosition o E0 T tau L B s hE d) (CentralSchedule.momentum s) := by
  intro t₀ t₁
  have h := interval_area_is_swept o E0 T tau L B s hE d t₀ t₁
  rwa [interval_area_time_formula o E0 T tau L B s hE d t₀ t₁] at h

end NewtonLimitDynamics.Polygon.GeneralForceArea
