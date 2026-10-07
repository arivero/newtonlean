import BarrowLib.Polygon.Finite
import BarrowLib.Polygon.SectorFan
import NewtonLimitDynamics.Historical.CompositionOfMotions
import ModernLib.Polygon.PathDefect
import ModernLib.Polygon.GeneralForceArea
import ModernLib.Polygon.GivenTrajectoryArea

/-! Historical result: area_law.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! NATP00089. De Motu Theorem I; finite multiplicity area and derived block comparison; limit remains open. -/
/-! Witness: NATP00089.
Source: docs/m1/NATP00089.xml
SHA-256: b91b58f8d0a79a18eb60d6a715a3952821aff4cdfabbb5a16625ff3e572bbc34
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par8
Anchor URLs: NATP00089.par8 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par8; NATP00089.par9 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par9
Proof-step correspondence: Finite equal-time inertial segments and parallel central deflections preserve the triangle areas; composition sums them. The passage then takes the polygon to a curve, which remains open.
-/
/- LATIN BEGIN NATP00089.par8
Theorema 1. Gyrantia omnia radijs ad centrum ductis areas temporibus proportionales describere.
LATIN END NATP00089.par8 -/
/- LATIN BEGIN NATP00089.par9
Dividatur tempus in partes æquales, et prima temporis parte describat corpus vi insita rectam AB. Idem secunda temporis parte si nil impedireta [note: a Hyp. 1.] rectà pergeret ad [del: [unclear: C] ] c describens lineam Bc æqualem ipsi AB adeo ut radijs AS, BS, cS ad centrum actis confectæ forent æquales areæ ASB, BSc. Verum ubi corpus venit ad B agat vis centripeta impulsu unico sed magno, faciat corpus [del: ] a recta Bc deflectere et pergere in recta BC. Ipsi BS parallela agatur cC occurrens BC in C et completa secunda temporis parte b [note: [del: b Hyp 3] [add: b Lem. 1.] ] corpus reperietur in C. Iunge SC et triangulum SBC ob parallelas SB, Cc æquale erit triangulo SBc atqu adeo etiam triangulo S [del: C] [add: A] B. Simili argumento si vis centripeta successivè agat in C, D, E &c, faciens corpus singulis temporis momentis singulas describere rectas CD, DE, EF &c triangulum S [del: B] CD triangulo SBC et SDE ipsi SCD et SEF ipsi SDE æquale erit. Æqualibus igitur te [del: ] [add: mp] oribus æquales areæ describuntur. Sunto jam hæc triangula numero infinita et infinitè parva, sic, ut singulis temporis momentis singula respondeant triangula, agente vi centripeta sine intermissione, & constabit proposit [del: ] [add: io] .
LATIN END NATP00089.par9 -/

namespace DeMotu1684.AreaLaw
open NewtonLimitDynamics.Polygon NewtonLimitDynamics
variable {Point Impulse : Type}

theorem natp00089_finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

theorem natp00089_finite_block_comparison (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

end DeMotu1684.AreaLaw

/-! NATP00090. De Motu Theorem I; no retrospective proposition numbering. -/
/-! Witness: NATP00090.
Source: docs/m1/NATP00090.xml
SHA-256: 790b468987fd8c7716d9d43197ec3a724f7f581ec8b6ed3998edc191b951f998
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par16
Anchor URLs: NATP00090.par16 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par16; NATP00090.par17 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17
Proof-step correspondence: Finite equal-time inertial segments and parallel central deflections preserve the triangle areas; composition sums them. The passage then takes the polygon to a curve, which remains open.
Historical dependency ledger for this exact witness:
- NATP00090.Law1 → NATP00090.T1; passage NATP00090.par17; witness 'De motu sphæricorum corporum in fluidis'; URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17; status explicit_dependency; confidence high.
- NATP00090.L1 → NATP00090.T1; passage NATP00090.par17; witness 'De motu sphæricorum corporum in fluidis'; URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00090.par16
Theorema 1. Gyrantia omnia radijs ad centrum ductis areas temporibus proportionales describere.
LATIN END NATP00090.par16 -/
/- LATIN BEGIN NATP00090.par17
Dividatur tempus in partes æquales, et prima temporis parte describat corpus vi insita rectam AB. Idem secunda temporis parte si nil impediret [del: ] a [note: a [del: Hypoth.] [add: Lex] 1.] rectà pergeret ad c describens lineam Bc æqualem ipsi AB adeo ut radijs AS, BS, cS ad centrum actis confectæ forent æquales areæ ASB, BSc. Verum ubi corpus venit ad B agat vis centripeta impulsu unico sed magno, faciat corpus a recta Bc deflectere et pergere in recta BC. Ipsi BS parallela agatur cC occurrens BC in C et completa secunda temporis parte [del: ] b [note: b Lem. 1.] corpus reperietur in C. Iunge SC et triangulum SBC ob parallelas SB, Cc æquale erit triangulo SBc at adeo etiam triangulo SAB. Simili argumento si vis centripeta successivè agat in C, D, E &c faciens corpus singulis temporis momentis singulas describere rectas CD, DE, EF &c triangulum SCD triangulo SBC et SDE ipsi SCD et SEF ipsi SDE æquale erit. Æqualibus igitur temporibus æquales areæ describuntur. Sunto jam hæc triangula numero infinita et infinitè parva, sic, ut singulis temporis momentis singula respondeant triangula, agente vi centripeta sine intermissione, et constabit propositio.
LATIN END NATP00090.par17 -/

namespace DeMotu1684.AreaLaw
open NewtonLimitDynamics.Polygon NewtonLimitDynamics
variable {Point Impulse : Type}

theorem natp00090_finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

theorem natp00090_finite_block_comparison (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

end DeMotu1684.AreaLaw

/-! 1687. Proposition I finite proof steps; full sector limit open. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par44
Anchor URLs: NATP00077.par44 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par44; NATP00077.par45 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45
Proof-step correspondence: The edition's Laws Corollary I is actually used with supplied inertia/additive-change predicates to construct the next vertex and derive equal triangles. Finite composition and radial separation identify ordinary local triangle-union area under explicit area rules. Passage to the given curve and its swept-sector area remains open.
Historical dependency ledger for this exact witness:
- P1687.Law1 → P1687.P1; passage NATP00077.par45; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status explicit_dependency; confidence high.
- P1687.Composition → P1687.P1; passage NATP00077.par45; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status explicit_dependency; confidence high.
- P1687.L3C4 → P1687.P1; passage NATP00077.par45; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status explicit_dependency; confidence high.
- NATP00089.T1 → P1687.P1; passage NATP00077.par45; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45; status editorial_interpretation; confidence high.
-/
/- LATIN BEGIN NATP00077.par44
Areas quas corpora in gyros acta radiis ad immobile centrum virium ductis describunt, & in planis immobilibus consistere, & esse temporibus proportionales.
LATIN END NATP00077.par44 -/
/- LATIN BEGIN NATP00077.par45
Dividatur tempus in partes æquales, & prima temporis parte describat corpus vi insita rectam AB. Idem secunda temporis parte, si nil impediret, recta pergeret ad c, (per Leg. I) describens lineam Bc æqualem ipsi AB, adeo ut radiis AS, BS, cS ad centrum actis, confectæ forent æquales areæ ASB, BSc. Verum ubi corpus venit ad B, agat viscentripeta impulsu unico sed magno, faciatq; corpus a recta Bc deflectere & pergere in recta BC. Ipsi BS parallela agatur cC occurrens BC in C, & completa secunda temporis parte, corpus (per Legum Corol. 1) reperietur in C, in eodem plano cum triangulo ASB. Junge SC, & triangulum SBC, ob parallelas SB, Cc, æquale erit triangulo SBc, atq; adeo etiam triangulo SAB. Simili argumento si vis centripeta successive agat in C, D, E, &c. faciens ut corpus singulis temporis particulis singulas describat rectas CD, DE EF, &c. jacebunt hæ in eodem plano, & triangulum SCD triangulo SBC & SDE ipsi SCD & SEF ipsi SDE æquale erit. Æqualibus igitur temporibus æquales areæ in plano immoto describuntur: & componendo, sunt arearum summæ quævis SADS, SAFS inter se, ut sunt tempora descriptionum. Augeatur jam numerus & minuatur latitudo triangulorum in infinitum, & eorum ultima perimeter ADF, (per Corollarium quartum Lemmatis tertii) erit linea curva; adeoq; vis centripeta qua corpus de tangente hujus curvæ perpetuo retrahitur, aget indesinenter; areæ vero quævis descriptæ SADS, SAFS temporibus descriptionum semper proportionales, erunt iisdem temporibus in hoc casu proportionales. Q.E.D.
LATIN END NATP00077.par45 -/

namespace Principia1687.PropositionI
open NewtonLimitDynamics.Polygon NewtonLimitDynamics
variable {Point Impulse : Type}

theorem finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

theorem finite_componendo (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

/-! Coordinate realization of the finite historical construction. Inertia
governs each drift and the directed impulse changes its arrival velocity.
The laws are independent mechanical premises; equality of triangle areas
and identification with a local geometric union are proved below. -/

def mechanicalCell
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) : TimeSubdivision.Point × TimeSubdivision.Point :=
  let q := motion s.1 s.2 h
  (q, update s.2 (TimeSubdivision.pointScale h (a q)))

def polygonState
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) : Nat → TimeSubdivision.Point × TimeSubdivision.Point
  | 0 => s
  | n+1 => mechanicalCell motion update a h (polygonState motion update a h s n)

def polygonVertex
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) : TimeSubdivision.Point :=
  (polygonState motion update a h s n).1

open TimeSubdivision in
/-- Newton's AB, Bc, BC step: the edition's Laws Corollary I locates C;
the central direction and the preceding Law I drift give equal triangles.
Neither equal areas nor an areal-product conservation law is a premise. -/
theorem two_triangle_step
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1687.Laws.InertialMotion motion)
    (hII : Principia1687.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (p v : TimeSubdivision.Point) (h : Fraction) :
    Fraction.equiv
      (TimeSubdivision.det (motion p v h)
        (motion (motion p v h) (update v (pointScale h (a (motion p v h)))) h))
      (TimeSubdivision.det p (motion p v h)) := by
  let q := motion p v h
  let j := pointScale h (a q)
  have hcor := Principia1687.Laws.corollary1_from_laws motion update hI hII q v j h
  have hj : Fraction.equiv (TimeSubdivision.det q j) (Fraction.ofInt 0) :=
    Fraction.equiv_trans (det_scale_right h q (a q))
      (Fraction.equiv_trans (Fraction.mul_equiv_left h (ha q)) (Fraction.mul_zero h))
  have hd : Fraction.equiv (TimeSubdivision.det q (Parallelogram.diagonal q (pointScale h v) (pointScale h j)))
      (Fraction.add (Fraction.mul h (TimeSubdivision.det q v)) (Fraction.mul h (TimeSubdivision.det q j))) := by
    simp only [Parallelogram.diagonal,TimeSubdivision.det,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf
    omega
  have hnext : Fraction.equiv
      (TimeSubdivision.det q (motion q (update v j) h))
      (Fraction.mul h (TimeSubdivision.det q v)) :=
    Fraction.equiv_trans (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ hcor)
      (Fraction.equiv_trans hd (Fraction.equiv_trans
        (Fraction.add_equiv_left _ (Fraction.equiv_trans (Fraction.mul_equiv_left h hj)
          (Fraction.mul_zero h))) (Fraction.add_zero _)))
  have hprior : Fraction.equiv (TimeSubdivision.det p q)
      (Fraction.mul h (TimeSubdivision.det p v)) :=
    Fraction.equiv_trans
      (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI p v h))
      (CentralSchedule.det_cell_area p v h)
  have hdrift : Fraction.equiv (TimeSubdivision.det q v) (TimeSubdivision.det p v) :=
    Fraction.equiv_trans (TimeSubdivision.det_congr (hI p v h)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) (CentralSchedule.det_drift p v h)
  exact Fraction.equiv_trans hnext
    (Fraction.equiv_trans (Fraction.mul_equiv_left h hdrift) (Fraction.equiv_symm hprior))

theorem polygon_triangle_equal
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1687.Laws.InertialMotion motion)
    (hII : Principia1687.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) :
    Fraction.equiv
      (TimeSubdivision.det (polygonVertex motion update a h s n) (polygonVertex motion update a h s (n+1)))
      (Fraction.mul h (CentralSchedule.momentum s)) := by
  induction n with
  | zero =>
    exact Fraction.equiv_trans
      (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI s.1 s.2 h))
      (CentralSchedule.det_cell_area s.1 s.2 h)
  | succ n ih =>
    exact Fraction.equiv_trans
      (two_triangle_step motion update hI hII a ha
        (polygonState motion update a h s n).1 (polygonState motion update a h s n).2 h) ih

/-- The historical finite construction now has an actual local sector-union
area, rather than only a multiplicity-counted fan sum. The half-plane and
area convention are explicit geometric premises; this is not the curved
trajectory or the limiting step of Proposition I. -/
theorem finite_geometric_sector
    (area : SectorFan.AreaRules)
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1687.Laws.InertialMotion motion)
    (hII : Principia1687.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (h : Fraction) (hh : 0 ≤ h.num)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hs : 0 ≤ (CentralSchedule.momentum s).num)
    (n : Nat) (hp : ∀ i, i ≤ n → 0 < (polygonVertex motion update a h s i).1.num) :
    area.HasArea (SectorFan.Region (polygonVertex motion update a h s) n)
      (Fraction.mul (BoundedIteration.time h n) (CentralSchedule.momentum s)).half := by
  have htriangle := polygon_triangle_equal motion update hI hII a ha h s
  have hregion := SectorFan.region_area area _ n hp (fun i _ =>
    Fraction.nonnegative_equiv (htriangle i) (Fraction.nonnegative_mul _ _ hh hs))
  apply area.congr_value _ _ _ ?_ hregion
  apply Fraction.equiv_trans
    (PolygonFanArea.sum_congr _ _ (fun i => RationalIntervals.half_equiv (htriangle i)) n)
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant (Fraction.mul h (CentralSchedule.momentum s)).half n)
  simp only [BoundedIteration.time,Fraction.equiv,Fraction.half,Fraction.mul,Fraction.ofInt]
  ac_nf

end Principia1687.PropositionI

/-! 1713. Proposition I finite proof steps; full sector limit open. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par50
Anchor URLs: NATP00082.par50 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par50; NATP00082.par51 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51
Proof-step correspondence: The edition's Laws Corollary I is actually used with supplied inertia/additive-change predicates to construct the next vertex and derive equal triangles. Finite composition and radial separation identify ordinary local triangle-union area under explicit area rules. Passage to the given curve and its swept-sector area remains open.
Historical dependency ledger for this exact witness:
- P1713.Law1 → P1713.P1; passage NATP00082.par51; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status explicit_dependency; confidence high.
- P1713.Composition → P1713.P1; passage NATP00082.par51; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status explicit_dependency; confidence high.
- P1713.L3C4 → P1713.P1; passage NATP00082.par51; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status explicit_dependency; confidence high.
- P1687.P1 → P1713.P1; passage NATP00082.par51; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51; status editorial_interpretation; confidence high.
-/
/- LATIN BEGIN NATP00082.par50
Areas, quas corpora in gyros acta radiis ad immobile centrum virium ductis describunt, & in planis immobilibus consistere, & esse temporibus proportionales.
LATIN END NATP00082.par50 -/
/- LATIN BEGIN NATP00082.par51
Dividatur tempus in partes æquales, & prima temporis parte describat corpus vi insita rectam AB. Idem secunda temporis parte, si nil impediret, recta pergeret ad c, (per Leg. I.) describens lineam Bc æqualem ipsi AB; adeo ut radiis AS, BS, cS ad centrum actis, confectæ forent æquales areæ ASB, BSc. Verum ubi corpus venit ad B, agat viscentripeta impulsu unico sed magno, effaciatque corpus a recta Bc declinet & pergat in recta BC. Ipsi S BS parallela agatur cC, occurrens BC in C; & completa secunda temporis parte, corpus (per Legum Corol. 1.) reperietur in C, in eodem plano cum triangulo ASB. Junge SC; & triangulum SBC, ob parallelas SB, Cc, æquale erit triangulo SBc, atque adeo etiam triangulo SAB. Simili argumento si vis centripeta successive agat in C, D, E, &c. faciens ut corpus singulis temporis particulis singulas describat rectas CD, DE, EF, &c. jacebunt hæ in eodem plano; & triangulum SCD triangulo SBC & SDE ipsi SCD & SEF ipsi SDE æquale erit. Æqualibus igitur temporibus æquales areæ in plano immoto describuntur: & componendo, sunt arearum summæ quævis SADS, SAFS inter se, ut sunt tempora descriptionum. Augeatur jam numerus & minuatur latitudo triangulorum in infinitum, & eorum ultima perimeter ADF, (per Corollarium quartum Lemmatis tertii) erit linea curva: adeoque vis centripeta, qua corpus de tangente hujus curvæ perpetuo retrahitur, aget indesinenter; areæ vero quævis descriptæ SADS, SAFS temporibus descriptionum semper proportionales, erunt iisdem temporibus in hoc casu proportionales. Q.E.D.
LATIN END NATP00082.par51 -/

namespace Principia1713.PropositionI
open NewtonLimitDynamics.Polygon NewtonLimitDynamics
variable {Point Impulse : Type}

theorem finite_equal_areas (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  all_unsigned_cell_areas g p q impulse n

theorem finite_componendo (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  positive_unsigned_area_comparison g p q impulse dt hdt start₁ start₂ m n hm hn

/-! Coordinate realization of the finite historical construction. Inertia
governs each drift and the directed impulse changes its arrival velocity.
The laws are independent mechanical premises; equality of triangle areas
and identification with a local geometric union are proved below. -/

def mechanicalCell
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) : TimeSubdivision.Point × TimeSubdivision.Point :=
  let q := motion s.1 s.2 h
  (q, update s.2 (TimeSubdivision.pointScale h (a q)))

def polygonState
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) : Nat → TimeSubdivision.Point × TimeSubdivision.Point
  | 0 => s
  | n+1 => mechanicalCell motion update a h (polygonState motion update a h s n)

def polygonVertex
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (a : CentralSchedule.Field) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) : TimeSubdivision.Point :=
  (polygonState motion update a h s n).1

open TimeSubdivision in
/-- Newton's AB, Bc, BC step: the edition's Laws Corollary I locates C;
the central direction and the preceding Law I drift give equal triangles.
Neither equal areas nor an areal-product conservation law is a premise. -/
theorem two_triangle_step
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1713.Laws.InertialMotion motion)
    (hII : Principia1713.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (p v : TimeSubdivision.Point) (h : Fraction) :
    Fraction.equiv
      (TimeSubdivision.det (motion p v h)
        (motion (motion p v h) (update v (pointScale h (a (motion p v h)))) h))
      (TimeSubdivision.det p (motion p v h)) := by
  let q := motion p v h
  let j := pointScale h (a q)
  have hcor := Principia1713.Laws.corollary1_from_laws motion update hI hII q v j h
  have hj : Fraction.equiv (TimeSubdivision.det q j) (Fraction.ofInt 0) :=
    Fraction.equiv_trans (det_scale_right h q (a q))
      (Fraction.equiv_trans (Fraction.mul_equiv_left h (ha q)) (Fraction.mul_zero h))
  have hd : Fraction.equiv (TimeSubdivision.det q (Parallelogram.diagonal q (pointScale h v) (pointScale h j)))
      (Fraction.add (Fraction.mul h (TimeSubdivision.det q v)) (Fraction.mul h (TimeSubdivision.det q j))) := by
    simp only [Parallelogram.diagonal,TimeSubdivision.det,pointAdd,pointScale,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
    ac_nf
    omega
  have hnext : Fraction.equiv
      (TimeSubdivision.det q (motion q (update v j) h))
      (Fraction.mul h (TimeSubdivision.det q v)) :=
    Fraction.equiv_trans (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ hcor)
      (Fraction.equiv_trans hd (Fraction.equiv_trans
        (Fraction.add_equiv_left _ (Fraction.equiv_trans (Fraction.mul_equiv_left h hj)
          (Fraction.mul_zero h))) (Fraction.add_zero _)))
  have hprior : Fraction.equiv (TimeSubdivision.det p q)
      (Fraction.mul h (TimeSubdivision.det p v)) :=
    Fraction.equiv_trans
      (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI p v h))
      (CentralSchedule.det_cell_area p v h)
  have hdrift : Fraction.equiv (TimeSubdivision.det q v) (TimeSubdivision.det p v) :=
    Fraction.equiv_trans (TimeSubdivision.det_congr (hI p v h)
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) (CentralSchedule.det_drift p v h)
  exact Fraction.equiv_trans hnext
    (Fraction.equiv_trans (Fraction.mul_equiv_left h hdrift) (Fraction.equiv_symm hprior))

theorem polygon_triangle_equal
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1713.Laws.InertialMotion motion)
    (hII : Principia1713.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (h : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (n : Nat) :
    Fraction.equiv
      (TimeSubdivision.det (polygonVertex motion update a h s n) (polygonVertex motion update a h s (n+1)))
      (Fraction.mul h (CentralSchedule.momentum s)) := by
  induction n with
  | zero =>
    exact Fraction.equiv_trans
      (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hI s.1 s.2 h))
      (CentralSchedule.det_cell_area s.1 s.2 h)
  | succ n ih =>
    exact Fraction.equiv_trans
      (two_triangle_step motion update hI hII a ha
        (polygonState motion update a h s n).1 (polygonState motion update a h s n).2 h) ih

/-- The historical finite construction now has an actual local sector-union
area, rather than only a multiplicity-counted fan sum. The half-plane and
area convention are explicit geometric premises; this is not the curved
trajectory or the limiting step of Proposition I. -/
theorem finite_geometric_sector
    (area : SectorFan.AreaRules)
    (motion : TimeSubdivision.Point → TimeSubdivision.Point → Fraction → TimeSubdivision.Point)
    (update : TimeSubdivision.Point → TimeSubdivision.Point → TimeSubdivision.Point)
    (hI : Principia1713.Laws.InertialMotion motion)
    (hII : Principia1713.Laws.AdditiveImpulse update)
    (a : CentralSchedule.Field) (ha : CentralSchedule.central a) (h : Fraction) (hh : 0 ≤ h.num)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hs : 0 ≤ (CentralSchedule.momentum s).num)
    (n : Nat) (hp : ∀ i, i ≤ n → 0 < (polygonVertex motion update a h s i).1.num) :
    area.HasArea (SectorFan.Region (polygonVertex motion update a h s) n)
      (Fraction.mul (BoundedIteration.time h n) (CentralSchedule.momentum s)).half := by
  have htriangle := polygon_triangle_equal motion update hI hII a ha h s
  have hregion := SectorFan.region_area area _ n hp (fun i _ =>
    Fraction.nonnegative_equiv (htriangle i) (Fraction.nonnegative_mul _ _ hh hs))
  apply area.congr_value _ _ _ ?_ hregion
  apply Fraction.equiv_trans
    (PolygonFanArea.sum_congr _ _ (fun i => RationalIntervals.half_equiv (htriangle i)) n)
  apply Fraction.equiv_trans (PolygonFanArea.sum_constant (Fraction.mul h (CentralSchedule.momentum s)).half n)
  simp only [BoundedIteration.time,Fraction.equiv,Fraction.half,Fraction.mul,Fraction.ofInt]
  ac_nf

end Principia1713.PropositionI

/-
===============================================================================
===============================================================================
===============================================================================
===============================================================================
===============================================================================
ANACHRONICAL PROOFS
-/

/-! NATP00089 conditional reconstructions (Latin in the primary witness section above). -/
namespace DeMotu1684.AreaLaw
open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.PathDefect

-- Modern dependency score: 2/7 (M=2, H=5; transitive project theorems/axioms).
theorem natp00089_polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry
-- Modern dependency score: 235/461 (M=235, H=226; transitive project theorems/axioms).
theorem natp00089_constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t
-- Modern dependency score: 243/471 (M=243, H=228; transitive project theorems/axioms).
theorem natp00089_constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁
-- Modern dependency score: 129/311 (M=129, H=182; transitive project theorems/axioms).
theorem natp00089_constructed_boundary_limit (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : TimeSubdivision.Point × TimeSubdivision.Point)
    (hE : 0<E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    CurveTrace.BoundaryLimit (fun m => CurveTrace.ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (CurveTrace.ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

end DeMotu1684.AreaLaw

/-! NATP00090 conditional reconstructions (Latin in the primary witness section above). -/
namespace DeMotu1684.AreaLaw
open NewtonLimitDynamics NewtonLimitDynamics.Polygon NewtonLimitDynamics.Polygon.PathDefect

-- Modern dependency score: 2/7 (M=2, H=5; transitive project theorems/axioms).
theorem natp00090_polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry
-- Modern dependency score: 235/461 (M=235, H=226; transitive project theorems/axioms).
theorem natp00090_constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t
-- Modern dependency score: 243/471 (M=243, H=228; transitive project theorems/axioms).
theorem natp00090_constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁
-- Modern dependency score: 129/311 (M=129, H=182; transitive project theorems/axioms).
theorem natp00090_constructed_boundary_limit (o : ForceClasses.CentralOracle)
    (E0 T tau L B : Fraction) (s : TimeSubdivision.Point × TimeSubdivision.Point)
    (hE : 0<E0.num) (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE) :
    CurveTrace.BoundaryLimit (fun m => CurveTrace.ImageTrace
      (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m))
      (CurveTrace.ImageTrace (GeneralForceTime.gammaPosition o E0 T tau L B s hE d)) :=
  GeneralForcePolygonCurve.constructed_polygon_boundary_limit o E0 T tau L B s hE d

end DeMotu1684.AreaLaw

/-! Principia1687.PropositionI conditional reconstructions (Latin in the primary witness section above). -/
namespace Principia1687.PropositionI
open NewtonLimitDynamics.Polygon NewtonLimitDynamics NewtonLimitDynamics.Polygon.PathDefect

/-- Modern conditional reconstruction for an independently supplied state curve.
`Consistency` gives rational samples and local residual control, not a fan law
or polygon agreement. The conclusions are all-interval fan proportionality
and vanishing nonnegative outer content between paths; ordinary geometric
sector-union identification remains open. -/
-- Modern dependency score: 241/470 (M=241, H=229; transitive project theorems/axioms).
theorem supplied_trajectory_fan_and_path_content
    (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime.BinaryTime T d.time_nonnegative → CauchyValues.Value)
    (c : GivenTrajectoryArea.Consistency o E0 T tau L B s hE d u) :
    SweptArea.Proportional T d.time_nonnegative (fun t => PositionValues.asPosition (u t))
      (CentralSchedule.momentum s) ∧
    ∃ covers : ∀ m, SquareOuterContent.Cover
        (MatchedRegion.Region T d.time_nonnegative
          (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m)
          (fun t => PositionValues.asPosition (u t)) m),
      ∀ eps : Fraction, 0 < eps.num → ∃ N, ∀ m, N ≤ m →
        CauchyValues.Within (SquareContentValues.contentValue _ (covers m)).val
          (CauchyValues.embed (BinaryTime.scalarState (Fraction.ofInt 0))) eps :=
  ⟨GivenTrajectoryArea.proportional_swept_area o E0 T tau L B s hE d u c,
    GivenTrajectoryArea.between_path_content_tends_zero o E0 T tau L B s hE d u c⟩

-- Modern dependency score: 2/7 (M=2, H=5; transitive project theorems/axioms).
theorem polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry

-- Modern dependency score: 235/461 (M=235, H=226; transitive project theorems/axioms).
theorem constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t

-- Modern dependency score: 243/471 (M=243, H=228; transitive project theorems/axioms).
theorem constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁

end Principia1687.PropositionI

/-! Principia1713.PropositionI conditional reconstructions (Latin in the primary witness section above). -/
namespace Principia1713.PropositionI
open NewtonLimitDynamics.Polygon NewtonLimitDynamics NewtonLimitDynamics.Polygon.PathDefect

/-- The same modern supplied-motion fan and path-content reconstruction, kept
separate for the 1713 witness. Its historical limiting step remains open. -/
-- Modern dependency score: 241/470 (M=241, H=229; transitive project theorems/axioms).
theorem supplied_trajectory_fan_and_path_content
    (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (u : BinaryTime.BinaryTime T d.time_nonnegative → CauchyValues.Value)
    (c : GivenTrajectoryArea.Consistency o E0 T tau L B s hE d u) :
    SweptArea.Proportional T d.time_nonnegative (fun t => PositionValues.asPosition (u t))
      (CentralSchedule.momentum s) ∧
    ∃ covers : ∀ m, SquareOuterContent.Cover
        (MatchedRegion.Region T d.time_nonnegative
          (GeneralForcePolygonCurve.polygonMap o E0 T s hE d.time_nonnegative m)
          (fun t => PositionValues.asPosition (u t)) m),
      ∀ eps : Fraction, 0 < eps.num → ∃ N, ∀ m, N ≤ m →
        CauchyValues.Within (SquareContentValues.contentValue _ (covers m)).val
          (CauchyValues.embed (BinaryTime.scalarState (Fraction.ofInt 0))) eps :=
  ⟨GivenTrajectoryArea.proportional_swept_area o E0 T tau L B s hE d u c,
    GivenTrajectoryArea.between_path_content_tends_zero o E0 T tau L B s hE d u c⟩

-- Modern dependency score: 2/7 (M=2, H=5; transitive project theorems/axioms).
theorem polygon_trajectory_defect_control
    (polygonTrajectoryArea budget : Fraction → Fraction) (hbudget : Vanishes budget)
    (hgeometry : PolygonTrajectoryEnclosure polygonTrajectoryArea budget) :
    Vanishes polygonTrajectoryArea :=
  polygon_trajectory_defect_vanishes polygonTrajectoryArea budget hbudget hgeometry

-- Modern dependency score: 235/461 (M=235, H=226; transitive project theorems/axioms).
theorem constructed_central_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t
      (GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t) ∧
    GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (HarmonicTimeRealization.timeCoordinate T d.time_nonnegative t)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_area_law o E0 T tau L B s hE d t

-- Modern dependency score: 243/471 (M=243, H=228; transitive project theorems/axioms).
theorem constructed_central_interval_area_law (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
    (s : TimeSubdivision.Point × TimeSubdivision.Point) (hE : 0 < E0.num)
    (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)
    (t₀ t₁ : BinaryTime.BinaryTime T d.time_nonnegative) :
    SweptArea.AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁) ∧
    GeneralForceArea.intervalAreaValue o E0 T tau L B s hE d t₀ t₁ =
      SecantValues.secantValue (CentralSchedule.momentum s).abs.half
        (SweptArea.intervalElapsedValue T d.time_nonnegative t₀ t₁)
        (CauchyValues.embed FanValues.zeroState) ∧
    Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
      (RationalEnclosure.level mesh)) :=
  GeneralForceArea.constructed_interval_area_law o E0 T tau L B s hE d t₀ t₁

end Principia1713.PropositionI
