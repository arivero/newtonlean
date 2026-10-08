import BarrowLib.Polygon.MotionCurveCover
import BarrowLib.Polygon.TriangleExchange

/-! Exact rational controls of the finite radial collar and cover interfaces.
These derive finite geometry under stated premises, not an area model or a
historical law. -/
namespace NewtonLimitDynamics.Polygon.MotionCurveCoverControls
open NewtonLimitDynamics TimeSubdivision HarmonicStability HarmonicTimeComparison
open HarmonicDyadic HarmonicTimeRealization ConvexCover PointBounds RadialSector SupportingTangents

private def z := Fraction.ofInt 0
private def one := Fraction.ofInt 1
private def quarter : Fraction := ⟨1,4,by decide⟩
private def fiveFour : Fraction := ⟨5,4,by decide⟩
private def xTerminal : Point := ray fiveFour quarter
private def eighth : Fraction := ⟨1,8,by decide⟩
private def nineEight : Fraction := ⟨9,8,by decide⟩
private def g (theta : Fraction) : Fraction := Fraction.add one theta
private def xMid : Point := ray nineEight eighth

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))

private theorem upper_terminal :
    SectorFan.Triangle (ray fiveFour z) (ray fiveFour quarter) xTerminal :=
  RadialSector.triangle_vertex_right _ _

private theorem outside_lower_terminal :
    ¬ SectorFan.Triangle (ray one z) (ray one quarter) xTerminal := by
  intro h
  obtain ⟨r,u,hr,hu,he⟩ := (triangle_radial _ _ _).mp h
  have he' := pointEquiv_trans he (pointEquiv_trans
    (pointScale_congr r (ray_lerp u one z quarter))
    (scale_ray r one (affine u z quarter)))
  have hx := he'.1
  change Fraction.equiv fiveFour (Fraction.mul r one) at hx
  simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,fiveFour,one] at hx
  dsimp [UnitInterval] at hr
  have hden := r.den_pos
  omega

theorem terminal_collar_bound :
    Fraction.le (pointNorm (pointSub xTerminal (ray one z)))
      (Fraction.add
        (Fraction.mul (durationDifference one fiveFour) (Fraction.add one z.abs))
        (Fraction.mul fiveFour (durationDifference z quarter))) :=
  RadialCollarCover.triangle_collar_ball z quarter one fiveFour xTerminal
    (by decide) (by decide) (by decide) upper_terminal outside_lower_terminal

theorem terminal_bound_is_sharp :
    Fraction.equiv (pointNorm (pointSub xTerminal (ray one z))) ⟨9,16,by decide⟩ ∧
    Fraction.equiv
      (Fraction.add
        (Fraction.mul (durationDifference one fiveFour) (Fraction.add one z.abs))
        (Fraction.mul fiveFour (durationDifference z quarter))) ⟨9,16,by decide⟩ := by
  constructor <;> decide

private def xEquivalent : Point := (⟨10,8,by decide⟩,⟨10,32,by decide⟩)

theorem equivalent_terminal_bound :
    Fraction.le (pointNorm (pointSub xEquivalent (ray one z)))
      (Fraction.add
        (Fraction.mul (durationDifference one fiveFour) (Fraction.add one z.abs))
        (Fraction.mul fiveFour (durationDifference z quarter))) := by
  have he : pointEquiv xEquivalent xTerminal := by decide
  apply RadialCollarCover.triangle_collar_ball z quarter one fiveFour xEquivalent
    (by decide) (by decide) (by decide)
  · exact RadialSector.triangle_congr_point he upper_terminal
  · intro h
    exact outside_lower_terminal
      (RadialSector.triangle_congr_point (pointEquiv_symm he) h)

private theorem upper_collapsed : SectorFan.Triangle (ray (Fraction.ofInt 2) z)
    (ray (Fraction.ofInt 2) z) (ray (Fraction.ofInt 2) z) :=
  RadialSector.triangle_vertex_left _ _

private theorem outside_lower_collapsed :
    ¬ SectorFan.Triangle (ray one z) (ray one z) (ray (Fraction.ofInt 2) z) := by
  intro h
  obtain ⟨r,u,hr,hu,he⟩ := (triangle_radial _ _ _).mp h
  have he' := pointEquiv_trans he (pointEquiv_trans
    (pointScale_congr r (ray_lerp u one z z))
    (scale_ray r one (affine u z z)))
  have hx := he'.1
  change Fraction.equiv (Fraction.ofInt 2) (Fraction.mul r one) at hx
  simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,one] at hx
  dsimp [UnitInterval] at hr
  have hden := r.den_pos
  omega

theorem collapsed_cell_bound :
    Fraction.le (pointNorm (pointSub (ray (Fraction.ofInt 2) z) (ray one z)))
      (Fraction.add
        (Fraction.mul (durationDifference one (Fraction.ofInt 2)) (Fraction.add one z.abs))
        (Fraction.mul (Fraction.ofInt 2) (durationDifference z z))) :=
  RadialCollarCover.triangle_collar_ball z z one (Fraction.ofInt 2) _
    (by decide) (by decide) (by decide) upper_collapsed outside_lower_collapsed

private theorem interior_curve_sector : sector g z quarter xMid := by
  refine ⟨eighth,by decide,by decide,one,⟨by decide,by decide⟩,?_⟩
  unfold xMid g
  constructor <;>
    simp [pointScale,ray,pointEquiv,Fraction.equiv,Fraction.add,Fraction.mul,
      one,eighth,nineEight,Fraction.ofInt]

private theorem interior_upper :
    SectorFan.Triangle (ray fiveFour z) (ray fiveFour quarter) xMid := by
  obtain ⟨v,hv,he⟩ := radial_vertex nineEight fiveFour eighth
    (by decide) (by decide) (by decide)
  obtain ⟨w,hw,hwt⟩ := interval_parameter z quarter eighth (by decide) (by decide)
  have hline : pointEquiv (lerp w (ray fiveFour z) (ray fiveFour quarter))
      (ray fiveFour eighth) :=
    pointEquiv_trans (ray_lerp w fiveFour z quarter) (ray_congr_slope fiveFour hwt)
  exact (triangle_radial _ _ _).mpr ⟨v,w,hv,hw,
    pointEquiv_trans he (pointScale_congr v (pointEquiv_symm hline))⟩

private theorem interior_outside_lower :
    ¬ SectorFan.Triangle (ray one z) (ray one quarter) xMid := by
  intro h
  obtain ⟨v,w,hv,hw,he⟩ := (triangle_radial _ _ _).mp h
  have he' := pointEquiv_trans he (pointEquiv_trans
    (pointScale_congr v (ray_lerp w one z quarter))
    (scale_ray v one (affine w z quarter)))
  have hx := he'.1
  change Fraction.equiv nineEight (Fraction.mul v one) at hx
  simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,nineEight,one] at hx
  dsimp [UnitInterval] at hv
  have hden := v.den_pos
  omega

theorem interior_nonlinear_collar_bound :
    Fraction.le (pointNorm (pointSub xMid (ray one z)))
      (Fraction.add
        (Fraction.mul (durationDifference one fiveFour) (Fraction.add one z.abs))
        (Fraction.mul fiveFour (durationDifference z quarter))) :=
  RadialCollarCover.triangle_collar_ball z quarter one fiveFour xMid
    (by decide) (by decide) (by decide) interior_upper interior_outside_lower

theorem interior_curve_coordinates :
    pointEquiv xMid (⟨9,8,by decide⟩,⟨9,64,by decide⟩) ∧
    Fraction.equiv (g eighth) nineEight := by
  constructor <;> decide

private def s0 : Point × Point := ((one,z),(one,one))
private theorem g_positive : 0 < (g z).num := by decide

theorem expected_cover_coefficients :
    Fraction.equiv
      (MotionSectorCover.coefficient one quarter (Fraction.ofInt 2) (Fraction.ofInt 3) s0)
      ⟨43,16,by decide⟩ ∧
    Fraction.equiv
      (MotionCurveCover.collarCoefficient one quarter (Fraction.ofInt 2) (Fraction.ofInt 3)
        g z quarter g_positive)
      ⟨195,16,by decide⟩ ∧
    Fraction.equiv
      (MotionCurveCover.coefficient one quarter (Fraction.ofInt 2) (Fraction.ofInt 2)
        (Fraction.ofInt 3) s0 g z quarter g_positive)
      ⟨367,64,by decide⟩ := by
  decide

theorem expected_cover_budgets :
    Fraction.equiv
      (MotionCurveCover.budget one quarter (Fraction.ofInt 2) (Fraction.ofInt 2)
        (Fraction.ofInt 3) s0 g z quarter g_positive 0)
      ⟨134689,512,by decide⟩ ∧
    Fraction.equiv
      (MotionCurveCover.budget one quarter (Fraction.ofInt 2) (Fraction.ofInt 2)
        (Fraction.ofInt 3) s0 g z quarter g_positive 1)
      ⟨134689,1024,by decide⟩ := by
  decide

private theorem interior_outside_chord :
    ¬ SectorFan.Triangle (ray one z) (ray fiveFour quarter) xMid := by
  intro h
  obtain ⟨u,v,hu,hv,hs,hx⟩ := h
  let w := durationDifference (Fraction.add u v) one
  have hw : 0 ≤ w.num := (difference_nonnegative_iff _ _).mpr hs
  have htotal : Fraction.equiv (Fraction.add u (Fraction.add w v)) one := by
    simp only [w,durationDifference,negF,Fraction.equiv,Fraction.add,one,Fraction.ofInt,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one]
    ac_nf
    omega
  have he : pointEquiv xMid
      (pointAdd (pointScale u (ray one z))
        (pointAdd (pointScale w (z,z)) (pointScale v (ray fiveFour quarter)))) := by
    apply pointEquiv_trans hx
    constructor <;>
      simp only [pointEquiv,pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
        z,Fraction.ofInt,Int.zero_mul,Int.mul_zero,Int.zero_add,Int.add_zero,
        Int.add_mul,Int.mul_add] <;> ac_nf
  have hAt := TriangleExchange.triangleAt_of_weights
    (ray one z) (z,z) (ray fiveFour quarter) xMid u w v
    hu hw hv htotal he
  have hp : 0 ≤ (det (pointSub (ray fiveFour quarter) (ray one z))
      (pointSub (z,z) (ray one z))).num := by decide
  have hq : 0 ≤ (det (pointSub (ray fiveFour quarter) (ray one z))
      (pointSub (ray fiveFour quarter) (ray one z))).num := by decide
  have hdet := SectorFan.triangle_right
    (pointSub (z,z) (ray one z))
    (pointSub (ray fiveFour quarter) (ray one z))
    (pointSub (ray fiveFour quarter) (ray one z))
    (pointSub xMid (ray one z)) hAt hp hq
  have hnegative : (det (pointSub (ray fiveFour quarter) (ray one z))
      (pointSub xMid (ray one z))).num < 0 := by decide
  omega

private def oneCell : MonotoneRectangles.Partition z quarter where
  count := 1
  positive_count := by decide
  nodes := fun k => if k = 0 then z else quarter
  first := by decide
  last := by decide
  ordered := by
    intro k hk
    have h : k = 0 := by omega
    subst k
    decide

theorem nonlinear_curve_chord_difference :
    RadialSector.between g oneCell xMid := by
  left
  refine ⟨interior_curve_sector,?_⟩
  rintro ⟨k,hk,htri⟩
  have h : k = 0 := by change k < 1 at hk; omega
  subst k
  have hleft : pointEquiv (ray (g (oneCell.nodes 0)) (oneCell.nodes 0)) (ray one z) := by decide
  have hright : pointEquiv (ray (g (oneCell.nodes 1)) (oneCell.nodes 1))
      (ray fiveFour quarter) := by decide
  obtain ⟨u,v,hu,hv,hs,he⟩ := htri
  apply interior_outside_chord
  exact ⟨u,v,hu,hv,hs,pointEquiv_trans he
    (pointAdd_congr (pointScale_congr u hleft) (pointScale_congr v hright))⟩

private def force : Point → Point := fun _ => (z,Fraction.ofInt 2)
private def curve (t : Fraction) : Point × Point :=
  ((Fraction.add one t,Fraction.add t (Fraction.mul t t)),
    (one,Fraction.add one (Fraction.mul (Fraction.ofInt 2) t)))

theorem noncentral_force_at_initial :
    (det (curve z).1 (force (curve z).1)).num ≠ 0 := by decide

theorem terminal_curve_point : pointEquiv (curve quarter).1 xTerminal := by decide

theorem terminal_curve_outside_mechanical_at_zero_level :
    MotionCurveCover.between force quarter curve 0 xTerminal := by
  right
  constructor
  · refine ⟨quarter,by decide,by decide,one,⟨by decide,by decide⟩,?_⟩
    have hc := terminal_curve_point
    have hscale : pointEquiv (pointScale one (curve quarter).1) (curve quarter).1 := by
      constructor <;>
        simp [pointScale,pointEquiv,Fraction.equiv,Fraction.mul,one,Fraction.ofInt]
    exact pointEquiv_trans (pointEquiv_symm hc) (pointEquiv_symm hscale)
  · rintro ⟨k,hk,htri⟩
    have h : k = 0 := by change k < 1 at hk; omega
    subst k
    let p0 := (BoundedIteration.run force (duration quarter 0) (curve z) 0).1
    let p1 := (BoundedIteration.run force (duration quarter 0) (curve z) 1).1
    have hp : 0 ≤ (det p0 p1).num := by decide
    have hq : 0 ≤ (det p1 p1).num := by decide
    have hdet := SectorFan.triangle_left p0 p1 p1 xTerminal htri hp hq
    have hn : (det xTerminal p1).num < 0 := by decide
    omega

theorem terminal_difference_point_covered :
    MotionCurveCover.cover force one quarter (Fraction.ofInt 2) (Fraction.ofInt 2)
      (Fraction.ofInt 3) curve g z quarter g_positive 0 xTerminal := by
  refine ⟨0,by decide,?_⟩
  unfold SquareContains
  decide

theorem terminal_point_rejects_zero_radius :
    ¬ SquareContains (ray one z) z xTerminal := by
  unfold SquareContains
  decide

example (area : TriangleContent.AreaRules) :
    ∃ A : Nat → Fraction,
      (∀ j, area.HasArea (MotionCurveCover.cover force one quarter (Fraction.ofInt 2)
        (Fraction.ofInt 2) (Fraction.ofInt 3) curve g z quarter g_positive j) (A j) ∧
        0 ≤ (A j).num ∧ Fraction.le (A j)
          (MotionCurveCover.budget one quarter (Fraction.ofInt 2) (Fraction.ofInt 2)
            (Fraction.ofInt 3) (curve z) g z quarter g_positive j)) ∧
      Exhaustion.VanishingDifference Fraction.magnitudes A :=
  MotionCurveCover.cover_areas area force one quarter (Fraction.ofInt 2) (Fraction.ofInt 2)
    (Fraction.ofInt 3) curve g z quarter g_positive
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end NewtonLimitDynamics.Polygon.MotionCurveCoverControls
