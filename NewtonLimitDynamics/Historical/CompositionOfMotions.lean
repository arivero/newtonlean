import BarrowLib.Polygon.ImpulseComposition
import NewtonLimitDynamics.Historical.LawI
import NewtonLimitDynamics.Historical.LawII

/-! Historical result: composition_of_motions.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! NATP00089. Hypothesis, modern finite model only; no historical proof asserted. -/
/-! Witness: NATP00089.
Source: docs/m1/NATP00089.xml
SHA-256: b91b58f8d0a79a18eb60d6a715a3952821aff4cdfabbb5a16625ff3e572bbc34
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par7
Anchor URLs: NATP00089.par7 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par7
Proof-step correspondence: The finite endpoint model proves the two transverse line constraints and their unique intersection for independent directions. Printed corollary sections also derive diagonal motion at every rational time from their own explicit Law I inertia and calibrated Law II additive-change premises. These premises are not proved from geometry; De Motu witnesses retain their separate hypothesis/model scope.
-/
/- LATIN BEGIN NATP00089.par7
[add: Hyp. 3. Corpus [del: minibus] in dato tempore viribus conjunctis eo ferri quo viribus divisis in temporibus æqualibus successivè. Hyp 4]
LATIN END NATP00089.par7 -/

namespace DeMotu1684.Composition
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision Parallelogram

theorem natp00089_composition_model (p u v : Point) (t : Fraction) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) :=
  ImpulseComposition.uniform_impulse_diagonal p u v t

end DeMotu1684.Composition

/-! NATP00090. Lemma I and proof. -/
/-! Witness: NATP00090.
Source: docs/m1/NATP00090.xml
SHA-256: 790b468987fd8c7716d9d43197ec3a724f7f581ec8b6ed3998edc191b951f998
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par10
Anchor URLs: NATP00090.par10 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par10; NATP00090.par11 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par11
Proof-step correspondence: This witness's supplied Lex 1 inertia and Lex 2 calibrated velocity difference derive the simultaneous endpoint's two transverse line constraints. For independent directions their unique intersection gives the diagonal, following the stated endpoint argument. The direct finite addition identity also covers parallel, opposite and zero impulses and zero elapsed time; this extension does not infer unique intersection of degenerate lines. The post-impulse uniform drift, fixed-body calibration and rational coordinates are explicit editorial model premises. The text literally says M acts along AC, although its setup places M along AB and N along AC. This witness-internal label inconsistency is retained in the Latin; the two vector roles are interpreted from the setup and the symmetric line argument, not silently corrected or replaced by 1687 wording. No printed-edition law is used, and NATP00089 remains separate.
Historical dependency ledger for this exact witness:
- NATP00090.Law2 → NATP00090.L1; passage NATP00090.par11; witness 'De motu sphæricorum corporum in fluidis'; URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par11; status explicit_dependency; confidence high.
- NATP00090.Law1 → NATP00090.L1; passage NATP00090.par5 ("uniformiter" in the revised reading) and par11 ("dato tempore" and the endpoint approach argument); witness 'De motu sphæricorum corporum in fluidis'; URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par11; status editorial_interpretation; confidence medium.
The model applies impulses initially and uses unimpeded uniform drift afterward. Par11 itself cites only Lex 2.
-/
/- LATIN BEGIN NATP00090.par10
Lemma 1 Corpus viribus conjunctis diagonalem parallelogramm [del: ] [add: i] eodem tempore describere quo latera separ [del: t] [add: a] tis.
LATIN END NATP00090.par10 -/
/- LATIN BEGIN NATP00090.par11
Si corpus dato tempore vi sola M ferretur ab A ad B et vi sola N ab A ad C, compleatur parallelogrammum ABDC et vi utra feretur id eodem tempore ab A ad D. Nam quoniam vis M agit secundum lineam AC ipsi BD parallelam, hæc vis [add: per Legem 2] nihil mutabit celeritatem accedendi ad lineam illam B [del: C] [add: D] vi altera impressam. Accedet igitur corpus eodem tempore ad lineam BD sive vis AC imprimatur sive non, at adeò in fine illius temporis reperietur alicubi in linea illa BD. Eodem argumento in fine temporis ejusdem reperietur alicubi in linea CD, et proinde in utrius lineæ concursu D reperiri necesse est.
LATIN END NATP00090.par11 -/

namespace DeMotu1684.Composition
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision Parallelogram

/-- Cancellation converts the supplied calibrated velocity difference into
addition; it is not a mechanical law derived from geometry. -/
private theorem natp00090_additive
    (update : Point → Point → Point) (hII : NATP00090.Laws.CalibratedChange update)
    (u j : Point) : pointEquiv (update u j) (pointAdd u j) := by
  have hc : pointEquiv (pointAdd u (pointSub (update u j) u)) (update u j) := by
    constructor <;>
      simp only [pointSub,pointNeg,pointAdd,Fraction.equiv,Fraction.add,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega
  exact pointEquiv_trans (pointEquiv_symm hc)
    (pointAdd_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (hII u j))

private theorem natp00090_uniform_after_change
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : NATP00090.Laws.InertialMotion motion)
    (hII : NATP00090.Laws.CalibratedChange update)
    (p u v : Point) (t : Fraction) (ht : 0 ≤ t.num) :
    pointEquiv (motion p (update u v) t)
      (ZeroForce.inertialAt p (pointAdd u v) t) :=
  pointEquiv_trans (hI p (update u v) t ht)
    (pointAdd_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
      (pointScale_congr t (natp00090_additive update hII u v)))

/-- The two endpoint-line constraints are derived from this witness's
mechanical premises, rather than supplied as the composition conclusion. -/
theorem natp00090_lemma1_endpoint_lines_from_laws
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : NATP00090.Laws.InertialMotion motion)
    (hII : NATP00090.Laws.CalibratedChange update)
    (p u v : Point) (t : Fraction) (ht : 0 ≤ t.num) :
    ParallelThrough (motion p (update u v) t)
      (ZeroForce.inertialAt p u t) (pointScale t v) ∧
    ParallelThrough (motion p (update u v) t)
      (ZeroForce.inertialAt p v t) (pointScale t u) := by
  have hm := natp00090_uniform_after_change motion update hI hII p u v t ht
  have hl := ImpulseComposition.uniform_endpoint_lines p u v t
  exact ⟨Fraction.equiv_trans (det_congr hm ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) hl.1,
    Fraction.equiv_trans (det_congr hm ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) hl.2⟩

/-- The source's two-line intersection argument, with its necessary
independence premise. The M/AC label inconsistency is recorded above. -/
theorem natp00090_lemma1_endpoint_from_laws
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : NATP00090.Laws.InertialMotion motion)
    (hII : NATP00090.Laws.CalibratedChange update)
    (p u v : Point) (t : Fraction) (ht : 0 ≤ t.num)
    (hind : (det (pointScale t u) (pointScale t v)).num ≠ 0) :
    pointEquiv (motion p (update u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) := by
  have hl := natp00090_lemma1_endpoint_lines_from_laws motion update hI hII p u v t ht
  exact ImpulseComposition.endpoint_from_components p (pointScale t u) (pointScale t v)
    (motion p (update u v) t) hind hl.1 hl.2

/-- Finite calibrated-motion extension covering dependent impulse
directions and zero time by addition, without degenerate-line uniqueness. -/
theorem natp00090_lemma1_from_laws
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : NATP00090.Laws.InertialMotion motion)
    (hII : NATP00090.Laws.CalibratedChange update)
    (p u v : Point) (t : Fraction) (ht : 0 ≤ t.num) :
    pointEquiv (motion p (update u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) :=
  pointEquiv_trans (natp00090_uniform_after_change motion update hI hII p u v t ht)
    (ImpulseComposition.uniform_impulse_diagonal p u v t)

theorem natp00090_lemma1_endpoint_reconstruction (p u v : Point) (t : Fraction)
    (h : (TimeSubdivision.det (pointScale t u) (pointScale t v)).num ≠ 0) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) := by
  have hl := ImpulseComposition.uniform_endpoint_lines p u v t
  exact ImpulseComposition.endpoint_from_components p (pointScale t u) (pointScale t v)
    (ZeroForce.inertialAt p (pointAdd u v) t) h hl.1 hl.2

end DeMotu1684.Composition

/-! 1687. Laws Corollary I. -/
/-! Witness: 1687.
Source: docs/m1/NATP00076.xml
SHA-256: fc2984820b61f64fdbf5efe1142ea8cf5458b75dd54fc6525f73ee705a8a9b1c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par7
Anchor URLs: NATP00076.par7 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par7; NATP00076.par8 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par8
Proof-step correspondence: The finite endpoint model proves the two transverse line constraints and their unique intersection for independent directions. Printed corollary sections also derive diagonal motion at every rational time from their own explicit Law I inertia and calibrated Law II additive-change premises. These premises are not proved from geometry; De Motu witnesses retain their separate hypothesis/model scope.
Historical dependency evidence for this exact witness:
- P1687.Law2 → P1687.Composition; passage NATP00076.par4 ("motui ejus ... additur ... componitur") and par8 ("nihil mutabit velocitatem"); witness Axiomata Sive Leges Motus (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par8; status implicit_dependency; confidence high.
- P1687.Law1 → P1687.Composition; passage NATP00076.par1 ("movendi uniformiter in directum") and par7 ("eodem tempore"); witness Axiomata Sive Leges Motus (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par7; status editorial_interpretation; confidence medium.
No numbered law is cited in par8. Uniform post-impulse drift is the formal model's explicit interpretation; par8 does not contain 1713's final Law I sentence.
-/
/- LATIN BEGIN NATP00076.par7
Corpus viribus conjunctis diagonalem parallelogrammi eodem tempore describere, quo latera separatis.
LATIN END NATP00076.par7 -/
/- LATIN BEGIN NATP00076.par8
Si corpus dato tempore, vi sola M, ferretur ab A ad B, & vi sola N, ab A ad C, compleatur parallelogrammum ABDC, & vi utraq; feretur id eodem tempore ab A ad D. Nam quoniam vis N agit secundum lineam AC ipsi BD parallelam, hæc vis nihil mutabit velocitatem accedendi ad lineam illam BD a vi altera genitam. Accedet igitur corpus eodem tempore ad lineam BD sive vis N imprimatur, sive non, atq; adeo in fine illius temporis reperietur alicubi in linea illa BD. Eodem argumento in fine temporis ejusdem reperietur alicubi in linea CD, & idcirco in utriusque lineæ concursu D reperiri necesse est.
LATIN END NATP00076.par8 -/

namespace Principia1687.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision Parallelogram

/-- At every rational elapsed time, initial directed additive impulses followed
by inertia describe the diagonal. The mechanical laws are explicit premises,
separate from the resulting parallelogram statement. -/
theorem corollary1_from_laws
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (p u v : Point) (t : Fraction) :
    pointEquiv (motion p (update u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) :=
  pointEquiv_trans (hI p (update u v) t)
    (pointEquiv_trans
      (pointAdd_congr ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩
        (pointScale_congr t (hII u v)))
      (ImpulseComposition.uniform_impulse_diagonal p u v t))

theorem corollary1_endpoint_reconstruction (p u v : Point) (t : Fraction)
    (h : (TimeSubdivision.det (pointScale t u) (pointScale t v)).num ≠ 0) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) := by
  have hl := ImpulseComposition.uniform_endpoint_lines p u v t
  exact ImpulseComposition.endpoint_from_components p (pointScale t u) (pointScale t v)
    (ZeroForce.inertialAt p (pointAdd u v) t) h hl.1 hl.2

theorem corollary1_uniform_impulse_model (p u v : Point) (t : Fraction) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) :=
  ImpulseComposition.uniform_impulse_diagonal p u v t

end Principia1687.Laws

/-! 1713. Laws Corollary I, with its own Laws I and II wording. -/
/-! Witness: 1713.
Source: docs/m1/NATP00081.xml
SHA-256: 5c72c73d9f396d3b34475543fa7cd158ab29006fb43fa35bc63df9b7e4be6bfe
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par7
Anchor URLs: NATP00081.par7 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par7; NATP00081.par8 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par8
Proof-step correspondence: The finite endpoint model proves the two transverse line constraints and their unique intersection for independent directions. Printed corollary sections also derive diagonal motion at every rational time from their own explicit Law I inertia and calibrated Law II additive-change premises. These premises are not proved from geometry; De Motu witnesses retain their separate hypothesis/model scope.
Historical dependency ledger for this exact witness:
- P1713.Law2 → P1713.Composition; passage NATP00081.par8; witness Axiomata Sive Leges Motus (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par8; status explicit_dependency; confidence high.
- P1713.Law1 → P1713.Composition; passage NATP00081.par8; witness Axiomata Sive Leges Motus (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par8; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00081.par7
Corpus viribus conjunctis diagonalem parallelogrammi eodem tempore describere, quo latera separatis.
LATIN END NATP00081.par7 -/
/- LATIN BEGIN NATP00081.par8
Si corpus dato tempore, vi sola M in loco A impressa, ferretur uniformi cum motu ab A ad B; & vi sola N in eodem loco impressa, ferretur ab A ad C: compleatur parallelogrammum ABDC, & vi utraque feretur id eodem tempore in diagonali ab A ad D. Nam quoniam vis N agit secundum lineam AC ipsi BD parallelam, hæc vis per Legem II nihil mutabit velocitatem accedendi ad lineam illam BD a vi altera genitam. Accedet igitur corpus eodem tempore ad lineam BD; sive vis N imprimatur, sive non; atque adeo in fine illius temporis reperietur alicubi in linea illa BD. Eodem argumento in fine temporis ejusdem reperietur alicubi in linea CD, & idcirco in utriusque lineae concursu D reperiri necesse est. Perget autem motu rectilineo ab A ad D per Legem I.
LATIN END NATP00081.par8 -/

namespace Principia1713.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision Parallelogram

/-- The edition's explicit Laws I and II premises yield the diagonal at every
rational time after impulses at the initial point, including dependent vectors. -/
theorem corollary1_from_laws
    (motion : Point → Point → Fraction → Point) (update : Point → Point → Point)
    (hI : InertialMotion motion) (hII : AdditiveImpulse update)
    (p u v : Point) (t : Fraction) :
    pointEquiv (motion p (update u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) :=
  pointEquiv_trans (hI p (update u v) t)
    (pointEquiv_trans
      (pointAdd_congr ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩
        (pointScale_congr t (hII u v)))
      (ImpulseComposition.uniform_impulse_diagonal p u v t))

theorem corollary1_endpoint_reconstruction (p u v : Point) (t : Fraction)
    (h : (TimeSubdivision.det (pointScale t u) (pointScale t v)).num ≠ 0) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) := by
  have hl := ImpulseComposition.uniform_endpoint_lines p u v t
  exact ImpulseComposition.endpoint_from_components p (pointScale t u) (pointScale t v)
    (ZeroForce.inertialAt p (pointAdd u v) t) h hl.1 hl.2

theorem corollary1_uniform_impulse_model (p u v : Point) (t : Fraction) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) ∧
    ParallelThrough (ZeroForce.inertialAt p (pointAdd u v) t)
      (ZeroForce.inertialAt p u t) (pointScale t v) ∧
    ParallelThrough (ZeroForce.inertialAt p (pointAdd u v) t)
      (ZeroForce.inertialAt p v t) (pointScale t u) :=
  ⟨ImpulseComposition.uniform_impulse_diagonal p u v t,
    ImpulseComposition.uniform_endpoint_lines p u v t⟩

end Principia1713.Laws
