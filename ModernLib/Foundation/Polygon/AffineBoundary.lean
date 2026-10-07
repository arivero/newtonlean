import ModernLib.Foundation.Polygon.BinaryCells

/-! Affine edges meeting at the same rational vertex assign the same completed
point to equivalent time addresses on their common boundary. -/

namespace NewtonLimitDynamics.Polygon.AffineValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic
open HarmonicAccumulation HarmonicTimeComparison HarmonicTimeRealization
open BinaryTime CauchyValues

-- Modern dependency score: 18/94 (M=18, H=76; transitive project theorems/axioms).
theorem edge_boundary_names (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (x v y u : Point) (m : Nat)
    (hbase : Fraction.equiv (timeApprox c T m)
      (Fraction.add (timeApprox b T m) (duration T m)))
    (hpoint : pointEquiv y (pointAdd x (pointScale (duration T m) v)))
    (htime : AddressEquiv T hT b c) :
    NameEquiv (edgeName b T hT x v m) (edgeName c T hT y u m) := by
  let V := Fraction.add (pointNorm v) (pointNorm u)
  have hV : 0 ≤ V.num := Fraction.nonnegative_add _ _
    (pointNorm_nonnegative v) (pointNorm_nonnegative u)
  intro eps heps
  obtain ⟨N,hN⟩ := addressEquiv_symm T hT htime (factorDelta V eps hV)
    (factorDelta_positive V eps hV heps)
  refine ⟨N, ?_⟩
  intro j hj
  let tb := timeApprox b T (m+j)
  let tc := timeApprox c T (m+j)
  let e := timeApprox c T m
  let gap := (durationDifference tb tc).abs
  have htb : Fraction.le tb e := Fraction.le_equiv_right
    (time_interval b T hT m j).2 (Fraction.equiv_symm hbase)
  have htc : Fraction.le e tc := (time_interval c T hT m j).1
  obtain ⟨hg1,hg2⟩ := difference_interval_gaps tb e tc htb htc
  have hstate : stateEquiv (affineState x v (duration T m)) (y,zeroPoint) :=
    ⟨pointEquiv_symm hpoint, ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩
  have hl1 : Fraction.equiv
      (distance ((edgeName b T hT x v m).approx j) (y,zeroPoint))
      (Fraction.mul (durationDifference tb e).abs (pointNorm v)) := by
    have he := stateNorm_equiv (stateSub_congr
      (s:=((edgeName b T hT x v m).approx j))
      ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
        ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩ hstate)
    apply Fraction.equiv_trans (Fraction.equiv_symm he)
    exact Fraction.equiv_trans
      (stateSub_norm_symm ((edgeName b T hT x v m).approx j)
        (affineState x v (duration T m)))
      (Fraction.equiv_trans (affine_distance x v (duration T m) _)
      (Fraction.mul_equiv (Fraction.abs_equiv
        (Fraction.equiv_trans (phase_end_difference _ _ _)
          (difference_congr (Fraction.equiv_refl tb) (Fraction.equiv_symm hbase))))
        (Fraction.equiv_refl _)))
  have hl := Fraction.le_equiv_left hl1
    (Fraction.mul_le_mul_nonnegative hg1 (pointNorm v) (pointNorm_nonnegative v))
  have hr1 : Fraction.equiv
      (distance ((edgeName c T hT y u m).approx j) (y,zeroPoint))
      (Fraction.mul (durationDifference e tc).abs (pointNorm u)) :=
    affine_vertex_distance y u _
  have hr := Fraction.le_equiv_left
    (Fraction.equiv_trans (stateSub_norm_symm (y,zeroPoint)
      ((edgeName c T hT y u m).approx j)) hr1)
    (Fraction.mul_le_mul_nonnegative hg2 (pointNorm u) (pointNorm_nonnegative u))
  have htri := Fraction.magnitudes.le_trans
    (stateSub_triangle ((edgeName b T hT x v m).approx j) (y,zeroPoint)
      ((edgeName c T hT y u m).approx j)) (Fraction.add_le_add hl hr)
  have hscaled := Fraction.le_equiv_right htri
    (Fraction.equiv_symm (Fraction.mul_add gap (pointNorm v) (pointNorm u)))
  have htimegap := Fraction.magnitudes.lt_of_le_lt
    (Fraction.le_of_equiv (Fraction.equiv_symm (timeState_distance c b T (m+j))))
    (hN (m+j) (by omega))
  exact Fraction.magnitudes.lt_of_le_lt hscaled
    (factor_control V eps gap hV (Fraction.abs_num_nonnegative _) htimegap)

end NewtonLimitDynamics.Polygon.AffineValues
