import NewtonLimitDynamics

/-!
Target: NATP00090 Lemma 1 derives the finite parallelogram motion from
its own Law 1 inertia and Law 2 calibrated directed change. NATP00090
Theorem 1 must use that lemma in the actual impulse-then-drift recurrence
and derive equal triangle areas and a local finite sector-union area.

May assume: a given inertial motion map; a velocity update whose difference
from the incoming velocity is the supplied calibrated directed impulse;
a central sampled field; elementary geometric area rules and, for ordinary
union area, a positive common half-plane and nonnegative orientation.
Must not assume: parallelogram motion, equal areas, polygon/curve agreement,
a curved-area law, or any printed-edition law or limiting lemma. The rational
calibration and discrete impulses are explicit editorial model premises.
NATP00089 remains separate; NATP00090's laws do not supply its hypotheses.
Inertia is required only at nonnegative rational elapsed times. Preserve
par11's literal M/AC label inconsistency and identify the vector roles as
an editorial interpretation; do not silently replace its M with N.

Exact controls: p=(2,0), u=(0,1), t=1; arrival B=(2,1), central impulse
j=(-2,-1), next arrival C=(0,1). Both doubled triangle areas are 2, so
both triangle areas are 1. Noncentral impulse (1,0) gives C=(3,2),
doubled area 1, and must fail equality. Test a half-time step, zero time,
opposite/parallel directions and equivalent rational representatives.
The control does not establish a continuous curve-limit passage.
-/

namespace DeMotu1684.NATP00090.Controls
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision

private def p (x y : Int) : Point := (Fraction.ofInt x, Fraction.ofInt y)
private def half : Fraction := ⟨1,2,by decide⟩
private def one : Fraction := Fraction.ofInt 1
private def zero : Fraction := Fraction.ofInt 0
private def initial : Point × Point := (p 2 0, p 0 1)

private theorem inertia : NATP00090.Laws.InertialMotion ZeroForce.inertialAt :=
  fun _ _ _ _ => ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩
private theorem change : NATP00090.Laws.CalibratedChange pointAdd :=
  pointSub_add_self_left_equiv

-- Both endpoint lines and their independent intersection are consequences
-- of the witness-local laws in this nondegenerate example.
example : Parallelogram.ParallelThrough
    (ZeroForce.inertialAt (p 2 1) (pointAdd (p 0 1) (p (-2) (-1))) one)
    (ZeroForce.inertialAt (p 2 1) (p 0 1) one) (pointScale one (p (-2) (-1))) ∧
    Parallelogram.ParallelThrough
    (ZeroForce.inertialAt (p 2 1) (pointAdd (p 0 1) (p (-2) (-1))) one)
    (ZeroForce.inertialAt (p 2 1) (p (-2) (-1)) one) (pointScale one (p 0 1)) :=
  DeMotu1684.Composition.natp00090_lemma1_endpoint_lines_from_laws
    ZeroForce.inertialAt pointAdd inertia change _ _ _ _ (by decide)

example : pointEquiv
    (ZeroForce.inertialAt (p 2 1) (pointAdd (p 0 1) (p (-2) (-1))) one)
    (p 0 1) :=
  pointEquiv_trans
    (DeMotu1684.Composition.natp00090_lemma1_endpoint_from_laws
      ZeroForce.inertialAt pointAdd inertia change _ _ _ _ (by decide) (by decide))
    (by decide)

-- One full impulse-then-drift cycle, with a central field sampled at B.
example : pointEquiv (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
    CentralSchedule.harmonic one initial 1) (p 2 1) := by decide
example : pointEquiv (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
    CentralSchedule.harmonic one initial 2) (p 0 1) := by decide
example : Fraction.equiv
    (det (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
      CentralSchedule.harmonic one initial 0)
      (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
        CentralSchedule.harmonic one initial 1)) (Fraction.ofInt 2) := by decide
example : Fraction.equiv
    (det (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
      CentralSchedule.harmonic one initial 1)
      (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
        CentralSchedule.harmonic one initial 2)) (Fraction.ofInt 2) :=
  Fraction.equiv_trans
    (NATP00090.AreaLaw.polygon_triangle_equal ZeroForce.inertialAt pointAdd
      inertia change CentralSchedule.harmonic CentralSchedule.harmonic_central
      one (by decide) initial 1) (by decide)

-- The half-step uses the calibrated kick h*a(B)=(-1,-1/4).
example : pointEquiv (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
    CentralSchedule.harmonic half initial 1) (Fraction.ofInt 2, half) := by decide
example : pointEquiv (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
    CentralSchedule.harmonic half initial 2) (⟨3,2,by decide⟩, ⟨7,8,by decide⟩) := by decide
example : Fraction.equiv
    (det (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
      CentralSchedule.harmonic half initial 1)
      (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
        CentralSchedule.harmonic half initial 2)) one :=
  Fraction.equiv_trans
    (NATP00090.AreaLaw.polygon_triangle_equal ZeroForce.inertialAt pointAdd
      inertia change CentralSchedule.harmonic CentralSchedule.harmonic_central
      half (by decide) initial 1) (by decide)

-- The noncentral kick j=(1,0) changes the second doubled area from 2 to 1.
example : pointEquiv
    (ZeroForce.inertialAt (p 2 1) (pointAdd (p 0 1) (p 1 0)) one) (p 3 2) := by decide
example : Fraction.equiv (det (p 2 1) (p 3 2)) one ∧
    ¬ Fraction.equiv (det (p 2 1) (p 3 2)) (Fraction.ofInt 2) := by decide

-- Direct addition handles zero duration and dependent vector directions;
-- the independent two-line intersection theorem is not invoked here.
example : pointEquiv
    (ZeroForce.inertialAt (p 7 2) (pointAdd (p 1 0) (p 2 0)) zero) (p 7 2) :=
  pointEquiv_trans
    (DeMotu1684.Composition.natp00090_lemma1_from_laws
      ZeroForce.inertialAt pointAdd inertia change _ _ _ _ (by decide)) (by decide)
example : pointEquiv
    (ZeroForce.inertialAt (p 7 2) (pointAdd (p 1 0) (p (-1) 0)) half) (p 7 2) :=
  pointEquiv_trans
    (DeMotu1684.Composition.natp00090_lemma1_from_laws
      ZeroForce.inertialAt pointAdd inertia change _ _ _ _ (by decide)) (by decide)
example : pointEquiv
    (ZeroForce.inertialAt (p 7 2) (pointAdd (p 1 0) (p 2 0)) half)
    (⟨17,2,by decide⟩, Fraction.ofInt 2) :=
  pointEquiv_trans
    (DeMotu1684.Composition.natp00090_lemma1_from_laws
      ZeroForce.inertialAt pointAdd inertia change _ _ _ _ (by decide)) (by decide)
example : Fraction.equiv half (⟨2,4,by decide⟩ : Fraction) := by decide
example : pointEquiv
    (ZeroForce.inertialAt (p 7 2) (pointAdd (p 1 0) (p 2 0))
      (⟨2,4,by decide⟩ : Fraction))
    (⟨17,2,by decide⟩, Fraction.ofInt 2) :=
  pointEquiv_trans
    (DeMotu1684.Composition.natp00090_lemma1_from_laws
      ZeroForce.inertialAt pointAdd inertia change _ _ _ _ (by decide)) (by decide)

-- For the two half-time cells, positivity of the three vertex x-coordinates
-- is computed from the actual recurrence. Orientation follows from the law.
private theorem halfplane_two : ∀ i, i ≤ 2 →
    0 < (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
      CentralSchedule.harmonic half initial i).1.num := by
  intro i hi
  have he : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases he with rfl | rfl | rfl <;> decide

example : ∀ i, i < 2 → 0 ≤
    (det (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
      CentralSchedule.harmonic half initial i)
      (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
        CentralSchedule.harmonic half initial (i+1))).num := by
  intro i _
  exact Fraction.nonnegative_equiv
    (NATP00090.AreaLaw.polygon_triangle_equal ZeroForce.inertialAt pointAdd
      inertia change CentralSchedule.harmonic CentralSchedule.harmonic_central
      half (by decide) initial i) (by decide)

example (area : SectorFan.AreaRules) :
    area.HasArea
      (SectorFan.Region
        (NATP00090.AreaLaw.polygonVertex ZeroForce.inertialAt pointAdd
          CentralSchedule.harmonic half initial) 2) one := by
  have ha := NATP00090.AreaLaw.finite_geometric_sector area ZeroForce.inertialAt pointAdd
    inertia change CentralSchedule.harmonic CentralSchedule.harmonic_central
    half (by decide) initial (by decide) 2 halfplane_two
  exact area.congr_value _ _ _ (by decide) ha

#print axioms DeMotu1684.Composition.natp00090_lemma1_from_laws
#print axioms NATP00090.AreaLaw.two_triangle_step
#print axioms NATP00090.AreaLaw.finite_geometric_sector
end DeMotu1684.NATP00090.Controls
