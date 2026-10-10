import BarrowLib.Polygon.ConvexCover
import BarrowLib.Polygon.SectorFan
import BarrowLib.Polygon.DyadicArithmetic
import BarrowLib.Common.FiniteCrossing

/-! A dyadic square cover of each rational origin triangle.
Source: the original English statement and Lean derivation in this file.
This is project mathematics, without historical textual support or a priority claim. -/
namespace NewtonLimitDynamics.Polygon.RadialTriangleCover
open NewtonLimitDynamics TimeSubdivision HarmonicDyadic HarmonicStability
open HarmonicTimeComparison HarmonicTimeRealization PointBounds ConvexCover

def centres (p : Point) (j k : Nat) : Point :=
  pointScale (countTime (Fraction.ofInt 1) j k) p

private theorem zero_count (j : Nat) :
    Fraction.equiv (countTime (Fraction.ofInt 1) j 0) (Fraction.ofInt 0) := by
  simp [countTime,Fraction.mul,Fraction.ofInt,Fraction.equiv]

private theorem last_count (j : Nat) :
    Fraction.equiv (countTime (Fraction.ofInt 1) j (blocks j))
      (Fraction.ofInt 1) :=
  blocks_duration (Fraction.ofInt 1) j

private theorem dyadic_crossing (j : Nat) (s : Fraction)
    (hs0 : 0 ≤ s.num) (hs1 : Fraction.le s (Fraction.ofInt 1)) :
    ∃ k, k < blocks j ∧
      Fraction.le (countTime (Fraction.ofInt 1) j k) s ∧
      Fraction.le s (countTime (Fraction.ofInt 1) j (k+1)) := by
  have hpos : 0 < blocks j := by unfold blocks; exact Nat.pow_pos (by decide)
  have hstart : Fraction.le (countTime (Fraction.ofInt 1) j 0) s :=
    Fraction.le_equiv_left (zero_count j)
      (by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hs0)
  have hend : Fraction.le s (countTime (Fraction.ofInt 1) j (blocks j)) :=
    Fraction.le_equiv_right hs1 (Fraction.equiv_symm (last_count j))
  obtain ⟨k,hk,hleft,hright⟩ := FanIntervalChain.rising_crossing
    (fun k => (countTime (Fraction.ofInt 1) j k).toRat) s.toRat (blocks j) hpos
    ((Fraction.le_iff_toRat _ _).mp hstart) ((Fraction.le_iff_toRat _ _).mp hend)
  exact ⟨k,hk,(Fraction.le_iff_toRat _ _).mpr hleft,
    (Fraction.le_iff_toRat _ _).mpr hright⟩

private theorem cell_gap (j k : Nat) (s : Fraction)
    (hlo : Fraction.le (countTime (Fraction.ofInt 1) j k) s)
    (hhi : Fraction.le s (countTime (Fraction.ofInt 1) j (k+1))) :
    0 ≤ (durationDifference (countTime (Fraction.ofInt 1) j k) s).num ∧
    Fraction.le (durationDifference (countTime (Fraction.ofInt 1) j k) s)
      (duration (Fraction.ofInt 1) j) := by
  let t := countTime (Fraction.ofInt 1) j k
  have h0 := (difference_nonnegative_iff t s).mpr hlo
  have h1 := Fraction.add_le_add_right hhi (negF t)
  change Fraction.le (durationDifference t s)
    (durationDifference t (countTime (Fraction.ofInt 1) j (k+1))) at h1
  have he : Fraction.equiv
      (durationDifference t (countTime (Fraction.ofInt 1) j (k+1)))
      (duration (Fraction.ofInt 1) j) :=
    Fraction.equiv_trans (countTime_difference (Fraction.ofInt 1) j k 1) (by
      simp [Fraction.equiv,Fraction.mul,Fraction.ofInt])
  exact ⟨h0,Fraction.le_equiv_right h1 he⟩

private theorem triangle_offset (p q x : Point) (u v t : Fraction)
    (hx : pointEquiv x (pointAdd (pointScale u p) (pointScale v q))) :
    pointEquiv (pointSub x (pointScale t p))
      (pointAdd (pointScale (durationDifference t (Fraction.add u v)) p)
        (pointScale v (pointSub q p))) := by
  have he := pointSub_congr hx
    (show pointEquiv (pointScale t p) (pointScale t p) from
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
  apply pointEquiv_trans he
  constructor <;>
    simp only [pointSub,pointNeg,pointAdd,pointScale,durationDifference,negF,
      Fraction.equiv,Fraction.add,Fraction.mul,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;>
    ac_nf <;> omega

private theorem triangle_cell_ball (p q x : Point) (R delta : Fraction)
    (hR : 0 ≤ R.num) (hdelta : 0 ≤ delta.num)
    (hp : Fraction.le (pointNorm p) R)
    (hq : Fraction.le (pointNorm (pointSub q p)) delta)
    (u v : Fraction) (hu : 0 ≤ u.num) (hv : 0 ≤ v.num)
    (hs : Fraction.le (Fraction.add u v) (Fraction.ofInt 1))
    (hx : pointEquiv x (pointAdd (pointScale u p) (pointScale v q)))
    (j k : Nat)
    (hlo : Fraction.le (countTime (Fraction.ofInt 1) j k) (Fraction.add u v))
    (hhi : Fraction.le (Fraction.add u v) (countTime (Fraction.ofInt 1) j (k+1))) :
    Fraction.le (pointNorm (pointSub x (centres p j k)))
      (Fraction.add delta (duration R j)) := by
  let t := countTime (Fraction.ofInt 1) j k
  let d := durationDifference t (Fraction.add u v)
  have hd := cell_gap j k (Fraction.add u v) hlo hhi
  have hv1 : Fraction.le v (Fraction.ofInt 1) :=
    Fraction.magnitudes.le_trans
      (Fraction.le_equiv_right (Fraction.le_add_nonnegative v u hu)
        (Fraction.add_comm v u)) hs
  have hde : Fraction.equiv d.abs d := Fraction.abs_of_nonnegative d hd.1
  have hve : Fraction.equiv v.abs v := Fraction.abs_of_nonnegative v hv
  have hnp : Fraction.le (pointNorm (pointScale d p)) (Fraction.mul d R) :=
    Fraction.le_equiv_left
      (Fraction.equiv_trans (pointNorm_scale d p)
        (Fraction.mul_equiv hde (Fraction.equiv_refl _)))
      (Fraction.mul_le_mul_nonnegative_left hp d hd.1)
  have hnq : Fraction.le (pointNorm (pointScale v (pointSub q p)))
      (Fraction.mul v delta) :=
    Fraction.le_equiv_left
      (Fraction.equiv_trans (pointNorm_scale v (pointSub q p))
        (Fraction.mul_equiv hve (Fraction.equiv_refl _)))
      (Fraction.mul_le_mul_nonnegative_left hq v hv)
  have hpart := Fraction.le_equiv_left
    (PointBounds.pointNorm_equiv (triangle_offset p q x u v t hx))
    (pointNorm_add_le (pointScale d p) (pointScale v (pointSub q p)))
  have hraw := Fraction.magnitudes.le_trans hpart (Fraction.add_le_add hnp hnq)
  have hmul := Fraction.add_le_add
    (Fraction.mul_le_mul_nonnegative hd.2 R hR)
    (Fraction.mul_le_mul_nonnegative hv1 delta hdelta)
  have htarget : Fraction.equiv
      (Fraction.add (Fraction.mul (duration (Fraction.ofInt 1) j) R)
        (Fraction.mul (Fraction.ofInt 1) delta))
      (Fraction.add delta (duration R j)) := by
    simp only [Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,duration,
      Int.add_mul,Int.mul_add]
    ac_nf
  exact Fraction.le_equiv_right (Fraction.magnitudes.le_trans hraw hmul) htarget

/-- Every point of a filled origin triangle lies in one of the dyadic
squares along its first radial edge. The second vertex may lie on either
side of that edge; no orientation or half-plane premise is needed. -/
theorem terminal_triangle_square_cover (p q x : Point) (R delta : Fraction)
    (hR : 0 ≤ R.num) (hdelta : 0 ≤ delta.num)
    (hp : Fraction.le (pointNorm p) R)
    (hq : Fraction.le (pointNorm (pointSub q p)) delta)
    (j : Nat) (hx : SectorFan.Triangle p q x) :
    SquareCover (centres p j) (Fraction.add delta (duration R j)) (blocks j) x := by
  obtain ⟨u,v,hu,hv,hs,hx⟩ := hx
  obtain ⟨k,hk,hlo,hhi⟩ := dyadic_crossing j (Fraction.add u v)
    (Fraction.nonnegative_add u v hu hv) hs
  refine ⟨k,hk,?_⟩
  exact ball_inside_square (centres p j k) x _
    (triangle_cell_ball p q x R delta hR hdelta hp hq
      u v hu hv hs hx j k hlo hhi)

end NewtonLimitDynamics.Polygon.RadialTriangleCover
