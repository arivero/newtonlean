import ModernLib.Foundation.Polygon.AffineBoundary
import ModernLib.Foundation.Polygon.PositionValues
import ModernLib.Foundation.Polygon.BinaryEndpoints

/-! A polygon on the constructed binary-time domain from actual finite
vertices with proved position joining. Alias invariance, zero-time values and
affine vertex bounds are shared independently of the map producing vertices.
There is no supplied curve, motion equation or convergence field. -/

namespace NewtonLimitDynamics.Polygon.PolygonValues
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicDyadic HarmonicBinaryPrefix
open HarmonicAccumulation HarmonicTimeComparison HarmonicTimeRealization BinaryTime
open CauchyValues PositionValues

structure VertexChain (T : Fraction) (m : Nat) where
  state : Nat → Point × Point
  join : ∀ k, pointEquiv (state (k+1)).1
    (pointAdd (state k).1 (pointScale (duration T m) (state k).2))

def polygonName (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num) (m : Nat)
    (v : VertexChain T m) : EndpointCauchyName :=
  AffineValues.edgeName b T hT (v.state (ticks b m)).1 (v.state (ticks b m)).2 m

def polygonPosition (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num) (m : Nat)
    (v : VertexChain T m) : PositionValue := asPosition (realize (polygonName b T hT m v))

-- Modern dependency score: 23/83 (M=23, H=60; transitive project theorems/axioms).
theorem polygon_same_cell (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m : Nat) (v : VertexChain T m) (hcell : ticks b m=ticks c m)
    (htime : AddressEquiv T hT b c) :
    polygonPosition b T hT m v = polygonPosition c T hT m v := by
  have hb : timeApprox b T m=timeApprox c T m := by simp only [timeApprox,hcell]
  unfold polygonPosition polygonName
  rw [hcell]
  exact congrArg asPosition (Quotient.sound
    (AffineValues.edgeName_same_start b c T hT _ _ m hb htime))

-- Modern dependency score: 31/109 (M=31, H=78; transitive project theorems/axioms).
theorem polygon_adjacent_cells (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m : Nat) (v : VertexChain T m) (hcell : ticks b m+1=ticks c m)
    (htime : AddressEquiv T hT b c) :
    polygonPosition b T hT m v = polygonPosition c T hT m v := by
  have hb : Fraction.equiv (timeApprox c T m)
      (Fraction.add (timeApprox b T m) (duration T m)) := by
    have hk := congrArg (fun n : Nat => (n:Int)) hcell
    simp only [Int.natCast_add,Int.natCast_one] at hk
    simpa only [hk,timeApprox] using Fraction.equiv_symm (coarse_upper b T m)
  have hx : pointEquiv (v.state (ticks c m)).1
      (pointAdd (v.state (ticks b m)).1 (pointScale (duration T m) (v.state (ticks b m)).2)) := by
    rw [← hcell]
    exact v.join (ticks b m)
  exact congrArg asPosition (Quotient.sound (AffineValues.edge_boundary_names
    b c T hT _ _ _ _ m hb hx htime))

-- Modern dependency score: 1/6 (M=1, H=5; transitive project theorems/axioms).
theorem zero_window_vertices (T : Fraction) (m : Nat) (v : VertexChain T m)
    (hz : T.num=0) : ∀ k, pointEquiv (v.state k).1 (v.state 0).1 := by
  intro k
  induction k with
  | zero => exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  | succ k ih =>
    have hj := v.join k
    have hp := AffineValues.affine_zero_phase (v.state k).1 (v.state k).2
      (duration T m) hz
    exact pointEquiv_trans (pointEquiv_trans hj hp.1) ih

-- Modern dependency score: 24/90 (M=24, H=66; transitive project theorems/axioms).
theorem polygon_zero_window (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m : Nat) (v : VertexChain T m) (hz : T.num=0) :
    polygonPosition b T hT m v = asPosition (embed ((v.state 0).1,AffineValues.zeroPoint)) := by
  apply congrArg asPosition
  apply Quotient.sound
  apply nameEquiv_of_levelwise_stateEquiv
  intro j
  have ht : (durationDifference (timeApprox b T m) (timeApprox b T (m+j))).num=0 := by
    simp only [durationDifference,HarmonicStability.negF,timeApprox,duration,
      Fraction.add,Fraction.mul,Fraction.ofInt,hz,Int.mul_zero,Int.zero_mul,Int.neg_zero,Int.zero_add]
  have hp := AffineValues.affine_zero_phase (v.state (ticks b m)).1 (v.state (ticks b m)).2 _ ht
  exact ⟨pointEquiv_trans hp.1 (zero_window_vertices T m v hz _),hp.2⟩

-- Modern dependency score: 43/124 (M=43, H=81; transitive project theorems/axioms).
theorem polygon_address_independent (b c : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m : Nat) (v : VertexChain T m) (htime : AddressEquiv T hT b c) :
    polygonPosition b T hT m v = polygonPosition c T hT m v := by
  by_cases hz : T.num=0
  · exact (polygon_zero_window b T hT m v hz).trans (polygon_zero_window c T hT m v hz).symm
  · have hpos : 0<T.num := by omega
    obtain hc | hc | hc := address_equiv_cell_cases b c T hT hpos m htime
    · exact polygon_same_cell b c T hT m v hc htime
    · exact polygon_adjacent_cells b c T hT m v hc htime
    · exact (polygon_adjacent_cells c b T hT m v hc (addressEquiv_symm T hT htime)).symm

def polygonMap (T : Fraction) (hT : 0 ≤ T.num) (m : Nat) (v : VertexChain T m) :
    BinaryTime T hT → PositionValue :=
  Quotient.lift (fun b => polygonPosition b T hT m v)
    (fun b c h => polygon_address_independent b c T hT m v h)

-- Modern dependency score: 41/104 (M=41, H=63; transitive project theorems/axioms).
theorem polygon_vertex_bound (b : Nat → Bool) (T : Fraction) (hT : 0 ≤ T.num)
    (m : Nat) (v : VertexChain T m) (V : Fraction)
    (hv : Fraction.le (pointNorm (v.state (ticks b m)).2) V) :
    Within (polygonPosition b T hT m v).val
      (positionValue (embed (v.state (ticks b m)))) (Fraction.mul (duration T m) V) := by
  have hr := Fraction.mul_le_mul_nonnegative_left hv (duration T m) hT
  apply within_mono _ _ _ _ hr
  exact positionValue_within _ _ _ (AffineValues.edge_vertex_bound b T hT _ _ m)

-- Modern dependency score: 46/128 (M=46, H=82; transitive project theorems/axioms).
theorem polygonMap_left (T : Fraction) (hT : 0 ≤ T.num) (m : Nat) (v : VertexChain T m) :
    polygonMap T hT m v (leftTime T hT) = embedPosition (v.state 0).1 := by
  apply Subtype.ext
  change positionValue (realize (polygonName leftAddress T hT m v)) =
    positionValue (embed ((v.state 0).1,zeroPoint))
  apply congrArg positionValue
  apply Quotient.sound
  apply nameEquiv_of_levelwise_stateEquiv
  intro j
  have h0 : ticks leftAddress m=0 := all_zero_ticks m
  have h1 : ticks leftAddress (m+j)=0 := all_zero_ticks (m+j)
  have hz : (durationDifference (timeApprox leftAddress T m)
      (timeApprox leftAddress T (m+j))).num=0 := by
    simp [timeApprox,h0,h1,durationDifference,HarmonicStability.negF,Fraction.add,Fraction.mul,Fraction.ofInt]
  change stateEquiv (AffineValues.affineState (v.state (ticks leftAddress m)).1
    (v.state (ticks leftAddress m)).2 _) ((v.state 0).1,zeroPoint)
  rw [h0]
  exact AffineValues.affine_zero_phase _ _ _ hz

end NewtonLimitDynamics.Polygon.PolygonValues
