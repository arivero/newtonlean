import BarrowLib.Polygon.RadialSector
import BarrowLib.Polygon.PointBounds

/-! A finite rational bound for one radial triangle collar.
Source: the original English statement and Lean derivation here. This is
project mathematics without historical textual support or priority claim. -/
namespace NewtonLimitDynamics.Polygon.RadialCollarCover
open NewtonLimitDynamics TimeSubdivision HarmonicStability HarmonicTimeComparison
open ConvexCover SupportingTangents PointBounds RadialSector

theorem cap_radial_bounds (a b R S : Fraction)
    (hab : Fraction.le a b) (hR : 0 < R.num) (hRS : Fraction.le R S)
    (x : Point)
    (hupper : SectorFan.Triangle (ray S a) (ray S b) x)
    (hlower : ¬ SectorFan.Triangle (ray R a) (ray R b) x) :
    ∃ rho t, Fraction.le R rho ∧ Fraction.le rho S ∧
      Fraction.le a t ∧ Fraction.le t b ∧ pointEquiv x (ray rho t) := by
  obtain ⟨r,u,hr,hu,hx⟩ := (triangle_radial _ _ _).mp hupper
  let t := affine u a b
  let rho := Fraction.mul r S
  have ht := affine_between u a b hu hab
  have he : pointEquiv x (ray rho t) :=
    pointEquiv_trans hx (pointEquiv_trans
      (pointScale_congr r (ray_lerp u S a b)) (scale_ray r S t))
  have hr1 : Fraction.le r (Fraction.ofInt 1) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hr.2
  have hSpos : 0 < S.num := positive_of_le R S hR hRS
  have hS0 : 0 ≤ S.num := by omega
  have hrhoS : Fraction.le rho S :=
    Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative hr1 S hS0) (by
      simp [Fraction.equiv,Fraction.mul,Fraction.ofInt])
  have hrho0 : 0 ≤ rho.num := Fraction.nonnegative_mul r S hr.1 hS0
  have hRrho : Fraction.le R rho := by
    by_cases hrev : Fraction.le rho R
    · obtain ⟨v,hv,hvpoint⟩ := radial_vertex rho R t hrho0 hR hrev
      obtain ⟨w,hw,hwpoint⟩ := interval_parameter a b t ht.1 ht.2
      have hline : pointEquiv (lerp w (ray R a) (ray R b)) (ray R t) :=
        pointEquiv_trans (ray_lerp w R a b) (ray_congr_slope R hwpoint)
      have hlow : SectorFan.Triangle (ray R a) (ray R b) x :=
        (triangle_radial _ _ _).mpr ⟨v,w,hv,hw,
          pointEquiv_trans he (pointEquiv_trans hvpoint
            (pointScale_congr v (pointEquiv_symm hline)))⟩
      exact False.elim (hlower hlow)
    · unfold Fraction.le at *
      omega
  exact ⟨rho,t,hRrho,hrhoS,ht.1,ht.2,he⟩

private theorem radial_offset_identity (rho R t a : Fraction) :
    pointEquiv (pointSub (ray rho t) (ray R a))
      (pointAdd
        (pointScale (durationDifference R rho) (ray (Fraction.ofInt 1) a))
        (pointScale (durationDifference a t) (Fraction.ofInt 0,rho))) := by
  constructor <;>
    simp only [pointSub,pointNeg,pointAdd,pointScale,ray,durationDifference,negF,
      Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;>
    ac_nf <;> omega

private theorem unit_ray_norm (a : Fraction) :
    Fraction.equiv (pointNorm (ray (Fraction.ofInt 1) a))
      (Fraction.add (Fraction.ofInt 1) a.abs) := by
  simp [pointNorm,ray,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.abs,Fraction.ofInt]

private theorem vertical_norm (rho : Fraction) (hrho : 0 ≤ rho.num) :
    Fraction.equiv (pointNorm (Fraction.ofInt 0,rho)) rho := by
  have hz : Fraction.equiv (Fraction.ofInt 0).abs (Fraction.ofInt 0) :=
    Fraction.abs_of_nonnegative _ (by decide)
  exact Fraction.equiv_trans
    (Fraction.add_equiv hz (Fraction.abs_of_nonnegative rho hrho))
    (Fraction.equiv_trans (Fraction.add_comm _ _) (Fraction.add_zero rho))

private theorem radial_offset_bound (a b R S rho t : Fraction) (x : Point)
    (hab : Fraction.le a b) (hR : 0 ≤ R.num) (hRS : Fraction.le R S)
    (hRrho : Fraction.le R rho) (hrhoS : Fraction.le rho S)
    (hat : Fraction.le a t) (htb : Fraction.le t b)
    (hx : pointEquiv x (ray rho t)) :
    Fraction.le (pointNorm (pointSub x (ray R a)))
      (Fraction.add
        (Fraction.mul (durationDifference R S)
          (Fraction.add (Fraction.ofInt 1) a.abs))
        (Fraction.mul S (durationDifference a b))) := by
  let d := durationDifference R rho
  let D := durationDifference R S
  let e := durationDifference a t
  let E := durationDifference a b
  have hd0 : 0 ≤ d.num := (difference_nonnegative_iff R rho).mpr hRrho
  have hD0 : 0 ≤ D.num := (difference_nonnegative_iff R S).mpr hRS
  have he0 : 0 ≤ e.num := (difference_nonnegative_iff a t).mpr hat
  have hE0 : 0 ≤ E.num := (difference_nonnegative_iff a b).mpr hab
  have hrho0 : 0 ≤ rho.num := Fraction.nonnegative_of_le hR hRrho
  have hS0 : 0 ≤ S.num := Fraction.nonnegative_of_le hrho0 hrhoS
  have hdD : Fraction.le d D := by
    have h := Fraction.add_le_add_right hrhoS (negF R)
    exact h
  have heE : Fraction.le e E := by
    have h := Fraction.add_le_add_right htb (negF a)
    exact h
  have hnormu := unit_ray_norm a
  have hnormu0 := pointNorm_nonnegative (ray (Fraction.ofInt 1) a)
  have hdu : Fraction.le
      (pointNorm (pointScale d (ray (Fraction.ofInt 1) a)))
      (Fraction.mul D (Fraction.add (Fraction.ofInt 1) a.abs)) := by
    have heq : Fraction.equiv
        (pointNorm (pointScale d (ray (Fraction.ofInt 1) a)))
        (Fraction.mul d (pointNorm (ray (Fraction.ofInt 1) a))) :=
      Fraction.equiv_trans (pointNorm_scale d _)
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative d hd0) (Fraction.equiv_refl _))
    exact Fraction.le_equiv_left heq
      (Fraction.le_equiv_right
        (Fraction.mul_le_mul_nonnegative hdD _ hnormu0)
        (Fraction.mul_equiv (Fraction.equiv_refl _) hnormu))
  have hev : Fraction.le
      (pointNorm (pointScale e (Fraction.ofInt 0,rho)))
      (Fraction.mul S E) := by
    have heq : Fraction.equiv
        (pointNorm (pointScale e (Fraction.ofInt 0,rho)))
        (Fraction.mul e rho) :=
      Fraction.equiv_trans (pointNorm_scale e _)
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative e he0) (vertical_norm rho hrho0))
    have h1 := Fraction.mul_le_mul_nonnegative heE rho hrho0
    have h2 := Fraction.mul_le_mul_nonnegative_left hrhoS E hE0
    exact Fraction.le_equiv_left heq
      (Fraction.le_equiv_right (Fraction.magnitudes.le_trans h1 h2)
        (Fraction.mul_comm E S))
  have hpoint := pointSub_congr hx
    (show pointEquiv (ray R a) (ray R a) from
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
  have hoffset := pointEquiv_trans hpoint (radial_offset_identity rho R t a)
  have hnorm := Fraction.le_equiv_left (pointNorm_equiv hoffset)
    (pointNorm_add_le
      (pointScale d (ray (Fraction.ofInt 1) a))
      (pointScale e (Fraction.ofInt 0,rho)))
  exact Fraction.magnitudes.le_trans hnorm (Fraction.add_le_add hdu hev)

/-- One finite radial collar cell lies in an explicit L1 ball around its
lower left vertex. Closed and collapsed slope intervals are included. -/
theorem triangle_collar_ball (a b R S : Fraction) (x : Point)
    (hab : Fraction.le a b) (hR : 0 < R.num) (hRS : Fraction.le R S)
    (hupper : SectorFan.Triangle (ray S a) (ray S b) x)
    (hlower : ¬ SectorFan.Triangle (ray R a) (ray R b) x) :
    Fraction.le (pointNorm (pointSub x (ray R a)))
      (Fraction.add
        (Fraction.mul (durationDifference R S)
          (Fraction.add (Fraction.ofInt 1) a.abs))
        (Fraction.mul S (durationDifference a b))) := by
  obtain ⟨rho,t,hRrho,hrhoS,hat,htb,hx⟩ :=
    cap_radial_bounds a b R S hab hR hRS x hupper hlower
  exact radial_offset_bound a b R S rho t x hab (by omega) hRS
    hRrho hrhoS hat htb hx

end NewtonLimitDynamics.Polygon.RadialCollarCover
