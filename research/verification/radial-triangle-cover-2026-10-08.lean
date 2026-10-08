import BarrowLib.Polygon.MotionSectorCover

/-! Exact controls for the derived dyadic terminal-triangle cover. Thin
triangles with p=(2,1), q=p+(0,2^-j) have radius 4*2^-j. Generic
barycentric points, the upper vertex, the origin, reversed vertex order,
a second vertex below p, final radial cells, a collapsed origin triangle
and both joined-square groups are included. A displaced point rejects zero
radius, and the joined groups have points outside the other group.
These checks share the Lean kernel and coordinate definitions; they assign
no sector-difference area and do not prove a model of the area convention. -/
namespace NewtonLimitDynamics.Polygon.RadialCoverControls
open NewtonLimitDynamics TimeSubdivision PointBounds HarmonicStability
open HarmonicDyadic HarmonicTimeComparison HarmonicTimeRealization ConvexCover
open RadialTriangleCover MotionSectorCover

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))

private def one := Fraction.ofInt 1
private def zero := Fraction.ofInt 0
private def p : Point := (Fraction.ofInt 2,one)
private def e : Point := (zero,one)
private def delta (j : Nat) : Fraction := duration one j
private def q (j : Nat) : Point := pointAdd p (pointScale (delta j) e)

private theorem delta_nonnegative (j : Nat) : 0 ≤ (delta j).num := by
  dsimp [delta,duration,one,Fraction.ofInt]
  omega

private theorem p_norm : Fraction.le (pointNorm p) (Fraction.ofInt 3) := by
  simp [p,one,pointNorm,Fraction.le,Fraction.abs,Fraction.add,Fraction.ofInt]

private theorem e_norm : Fraction.equiv (pointNorm e) one := by
  unfold e one zero pointNorm
  decide

private theorem q_offset (j : Nat) :
    Fraction.le (pointNorm (pointSub (q j) p)) (delta j) := by
  have he := drift_offset (delta j) p e
  have hn := pointNorm_equiv he
  have hs := pointNorm_scale (delta j) e
  have ha := Fraction.abs_of_nonnegative (delta j) (delta_nonnegative j)
  have htarget : Fraction.equiv
      (Fraction.mul (delta j).abs (pointNorm e)) (delta j) := by
    apply Fraction.equiv_trans (Fraction.mul_equiv ha e_norm)
    simp [Fraction.equiv,Fraction.mul,one,Fraction.ofInt]
  exact Fraction.le_of_equiv (Fraction.equiv_trans hn (Fraction.equiv_trans hs htarget))

private def thinRadius (j : Nat) : Fraction :=
  Fraction.add (delta j) (duration (Fraction.ofInt 3) j)

private theorem thin_radius_four (j : Nat) :
    Fraction.equiv (thinRadius j) (duration (Fraction.ofInt 4) j) := by
  simp only [thinRadius,delta,one,duration,Fraction.equiv,Fraction.add,Fraction.ofInt,
    Int.add_mul,Int.mul_add]
  ac_nf
  omega

theorem thin_triangle_cover (j : Nat) (x : Point)
    (hx : SectorFan.Triangle p (q j) x) :
    SquareCover (centres p j) (duration (Fraction.ofInt 4) j) (blocks j) x := by
  obtain ⟨k,hk,hsq⟩ := terminal_triangle_square_cover p (q j) x
    (Fraction.ofInt 3) (delta j) (by decide) (delta_nonnegative j)
    p_norm (q_offset j) j hx
  exact ⟨k,hk,MotionSectorCover.square_radius_mono _ x
    (Fraction.le_of_equiv (thin_radius_four j)) hsq⟩

theorem reversed_triangle_cover (j : Nat) (x : Point)
    (hx : SectorFan.Triangle (q j) p x) :
    SquareCover (centres p j) (duration (Fraction.ofInt 4) j) (blocks j) x :=
  thin_triangle_cover j x ((SectorFan.triangle_swap (q j) p x).mp hx)

theorem upper_vertex_cover (j : Nat) :
    SquareCover (centres p j) (duration (Fraction.ofInt 4) j) (blocks j) (q j) :=
  thin_triangle_cover j (q j) (RadialSector.triangle_vertex_right p (q j))

private theorem origin_in_triangle (j : Nat) :
    SectorFan.Triangle p (q j) (zero,zero) := by
  refine ⟨zero,zero,by decide,by decide,by decide,?_⟩
  constructor <;> simp [pointScale,pointAdd,pointEquiv,Fraction.equiv,
    Fraction.mul,Fraction.add,zero,Fraction.ofInt]

theorem origin_cover (j : Nat) :
    SquareCover (centres p j) (duration (Fraction.ofInt 4) j) (blocks j) (zero,zero) :=
  thin_triangle_cover j _ (origin_in_triangle j)

theorem final_cell_zero_level :
    SquareContains (centres p 0 0) (duration (Fraction.ofInt 4) 0) (q 0) := by
  unfold SquareContains
  decide

theorem final_cell_first_level :
    SquareContains (centres p 1 1) (duration (Fraction.ofInt 4) 1) (q 1) := by
  unfold SquareContains
  decide

theorem displaced_upper_rejects_zero_radius :
    ¬ SquareContains (centres p 0 0) zero (q 0) := by
  unfold SquareContains
  decide

theorem upper_vertex_reversed_orientation (j : Nat) :
    SquareCover (centres p j) (duration (Fraction.ofInt 4) j) (blocks j) (q j) := by
  apply reversed_triangle_cover j (q j)
  exact (SectorFan.triangle_swap p (q j) (q j)).mp
    (RadialSector.triangle_vertex_right p (q j))

private def below : Point := (Fraction.ofInt 2,zero)

example : Fraction.equiv (det p below) (Fraction.ofInt (-2)) := by decide

theorem negative_determinant_triangle_cover (j : Nat) :
    SquareCover (centres p j) (Fraction.add one (duration (Fraction.ofInt 3) j))
      (blocks j) below := by
  exact terminal_triangle_square_cover p below below (Fraction.ofInt 3) one
    (by decide) (by decide) p_norm (by unfold pointNorm; decide) j
    (RadialSector.triangle_vertex_right p below)

private def origin : Point := (zero,zero)

theorem collapsed_origin_cover (j : Nat) :
    SquareCover (centres origin j) (Fraction.add zero (duration zero j))
      (blocks j) origin := by
  have hp : Fraction.le (pointNorm origin) zero := by
    simp [origin,zero,pointNorm,Fraction.le,Fraction.abs,Fraction.add,Fraction.ofInt]
  have hq : Fraction.le (pointNorm (pointSub origin origin)) zero :=
    Fraction.le_of_equiv (ConvexCover.pointSub_self_zero origin)
  exact terminal_triangle_square_cover origin origin origin zero zero
    (by decide) (by decide) hp hq j
    (RadialSector.triangle_vertex_left origin origin)

private def far : Point := (Fraction.ofInt 10,Fraction.ofInt 10)

theorem joined_left_branch :
    SquareCover (joinedCentres (fun _ => far) (centres p 0) 1)
      (duration (Fraction.ofInt 4) 0) 2 far := by
  apply (joined_cover (fun _ => far) (centres p 0)
    (duration (Fraction.ofInt 4) 0) 1 far).mpr
  exact Or.inl ⟨0,by decide,by unfold SquareContains; decide⟩

theorem joined_right_branch :
    SquareCover (joinedCentres (fun _ => far) (centres p 0) 1)
      (duration (Fraction.ofInt 4) 0) 2 (q 0) := by
  apply (joined_cover (fun _ => far) (centres p 0)
    (duration (Fraction.ofInt 4) 0) 1 (q 0)).mpr
  exact Or.inr ⟨0,by decide,final_cell_zero_level⟩

theorem joined_branches_distinct :
    ¬ SquareContains far (duration (Fraction.ofInt 4) 0) (q 0) ∧
      ¬ SquareContains (centres p 0 0) (duration (Fraction.ofInt 4) 0) far := by
  constructor <;> unfold SquareContains <;> decide

end NewtonLimitDynamics.Polygon.RadialCoverControls
