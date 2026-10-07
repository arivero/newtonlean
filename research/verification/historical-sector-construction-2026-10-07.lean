import NewtonLimitDynamics

/-! Controls for the source-local, law-driven finite sector construction.
The mechanical implementations change rational displays, so the result must
use value equivalence rather than equality of coordinate representatives. -/
namespace NewtonLimitDynamics.Polygon.HistoricalSectorControls
open NewtonLimitDynamics TimeSubdivision SectorFan CentralSchedule

private def f (x : Int) (d : Nat) : Fraction := ⟨x,d+1,by omega⟩
private def p (x y : Int) : Point := (Fraction.ofInt x,Fraction.ofInt y)
private def h : Fraction := f 1 1
private def s : Point × Point := (p 1 0,p 0 1)
private def alias (x : Fraction) : Fraction := ⟨2*x.num,2*x.den,Int.mul_pos (by decide) x.den_pos⟩
private def display (x : Point) : Point := (alias x.1,alias x.2)
private theorem display_equiv (x : Point) : pointEquiv (display x) x := by
  constructor <;> simp only [display,alias,Fraction.equiv] <;> ac_nf

private def motion (p v : Point) (t : Fraction) : Point := display (ZeroForce.inertialAt p v t)
private def update (u v : Point) : Point := display (pointAdd u v)
private theorem inertia1687 : Principia1687.Laws.InertialMotion motion :=
  fun _ _ _ => display_equiv _
private theorem impulse1687 : Principia1687.Laws.AdditiveImpulse update :=
  fun _ _ => display_equiv _
private theorem inertia1713 : Principia1713.Laws.InertialMotion motion :=
  fun _ _ _ => display_equiv _
private theorem impulse1713 : Principia1713.Laws.AdditiveImpulse update :=
  fun _ _ => display_equiv _

-- These functions actually change the displays while preserving the laws.
example : motion (p 1 0) (p 0 1) h ≠ ZeroForce.inertialAt (p 1 0) (p 0 1) h := by
  intro he
  have hd := congrArg (fun x : Point => x.1.den) he
  change (4 : Int) = 2 at hd
  omega

example : Fraction.equiv
    (TimeSubdivision.det (Principia1687.PropositionI.polygonVertex motion update harmonic h s 1)
      (Principia1687.PropositionI.polygonVertex motion update harmonic h s 2)) h :=
  Fraction.equiv_trans
    (Principia1687.PropositionI.polygon_triangle_equal motion update inertia1687 impulse1687
      harmonic harmonic_central h s 1) (by decide)

example (area : AreaRules) :
    area.HasArea (Region (Principia1687.PropositionI.polygonVertex motion update harmonic h s) 2) h := by
  have ha := Principia1687.PropositionI.finite_geometric_sector area motion update
    inertia1687 impulse1687 harmonic harmonic_central h (by decide) s (by decide) 2
    (by
      intro i hi
      have he : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases he with rfl | rfl | rfl <;> decide)
  exact area.congr_value _ _ _ (by decide) ha

example (area : AreaRules) :
    area.HasArea (Region (Principia1713.PropositionI.polygonVertex motion update harmonic h s) 2) h := by
  have ha := Principia1713.PropositionI.finite_geometric_sector area motion update
    inertia1713 impulse1713 harmonic harmonic_central h (by decide) s (by decide) 2
    (by
      intro i hi
      have he : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases he with rfl | rfl | rfl <;> decide)
  exact area.congr_value _ _ _ (by decide) ha

#print axioms Principia1687.PropositionI.two_triangle_step
#print axioms Principia1687.PropositionI.finite_geometric_sector
#print axioms Principia1713.PropositionI.finite_geometric_sector
end NewtonLimitDynamics.Polygon.HistoricalSectorControls
