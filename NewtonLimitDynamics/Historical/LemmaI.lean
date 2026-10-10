import BarrowLib.Common.Exhaustion
import BarrowLib.Common.RationalMagnitudes
/-! Historical result: lemma_i.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Exhaustion contradiction with explicit terminal comparisons. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par1
Anchor URLs: NATP00077.par1 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par1; NATP00077.par2 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par2
Proof-step correspondence: A supposed positive ultimate difference has a smaller positive comparison. Unlimited approach supplies a stage below that comparison, while the terminal lower comparison supplies a common later stage above it. Strict order contradicts this. Terminal values are supplied, not constructed.
-/
/- LATIN BEGIN NATP00077.par1
QVantitates, ut & quantitatum rationes, quæ ad æqualitatem dato tempore constanter tendunt & eo pacto propius ad invicem accedere possunt quam pro data quavis differentia; fiunt ultimo æquales.
LATIN END NATP00077.par1 -/
/- LATIN BEGIN NATP00077.par2
Si negas, sit earum ultima differentia D. Ergo nequeunt propius ad æqualitatem accedere quam pro data differentia D: contra hypothesin.
LATIN END NATP00077.par2 -/

namespace Principia1687.LemmaI
open NewtonLimitDynamics

/-- A sequence indexes successively closer approaches in the given time.
`TerminalLower` is the explicit interpretation of "ultima differentia";
the time parameterization and existence of ultimate values are not proved.
The conclusion is the absence of a positive ultimate difference. -/
theorem no_positive_ultimate_difference {Q : Type} (g : Magnitudes Q)
    (gap : Nat → Q) (D : Q)
    (hsmall : Exhaustion.VanishingDifference g gap)
    (hterminal : Exhaustion.TerminalLower g gap D) : ¬ g.positive D :=
  Exhaustion.no_positive_terminal g gap D hsmall hterminal

/-- The given positive duration is part of the formal premises. Remaining
time is strictly positive and less than that duration at the contradiction
witness; terminal comparisons and arbitrary closeness are supplied separately. -/
theorem given_time_exhaustion {Q : Type} (g : Magnitudes Q) (T : Q)
    (hT : g.positive T) (gap : Q → Q) (D : Q)
    (hsmall : ∀ d, g.positive d → Exhaustion.BeforeEnd g T (fun h => g.lt (gap h) d))
    (hterminal : ∀ d, g.positive d → g.lt d D →
      Exhaustion.BeforeEnd g T (fun h => g.lt d (gap h))) : ¬ g.positive D :=
  Exhaustion.no_positive_terminal_before_end g T hT gap D hsmall hterminal

/-- For a nonnegative rational terminal difference, absence of a positive
difference gives equality to zero. No ultimate equality is a premise. -/
theorem ultimate_difference_zero (gap : Nat → Fraction) (D : Fraction)
    (hD : 0 ≤ D.num)
    (hsmall : Exhaustion.VanishingDifference Fraction.magnitudes gap)
    (hterminal : Exhaustion.TerminalLower Fraction.magnitudes gap D) :
    Fraction.equiv D (Fraction.ofInt 0) := by
  have hn := no_positive_ultimate_difference Fraction.magnitudes gap D hsmall hterminal
  have hz : D.num = 0 := by change ¬ 0 < D.num at hn; omega
  simp only [Fraction.equiv, Fraction.ofInt, Int.mul_one, Int.zero_mul, hz]

end Principia1687.LemmaI

/-! 1713. Separate before-end exhaustion reconstruction. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par2
Anchor URLs: NATP00082.par2 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par2; NATP00082.par3 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par3
Proof-step correspondence: The same strict-order contradiction is applied to a succession of before-end approximations. The finite endpoint and its time parameterization remain explicit interpretive premises; no Cauchy completion or equality premise is used.
-/
/- LATIN BEGIN NATP00082.par2
QUantitates, ut & quantitatum rationes, quæ ad æqualitatem tempore quovis finito constanter tendunt, & ante finem temporis illius propius ad invicem accedunt quam pro data quavis differentia, fiunt ultimo æquales.
LATIN END NATP00082.par2 -/
/- LATIN BEGIN NATP00082.par3
Si negas; fiant ultimo inequales, & sit earum ultima differentia D. Ergo nequeunt propius ad æqualitatem accedere quam pro data differentia D: contra hypothesin.
LATIN END NATP00082.par3 -/

namespace Principia1713.LemmaI
open NewtonLimitDynamics

/-- The refinement indices represent approaches before the finite endpoint.
This edition does not inherit the 1687 theorem as a historical dependency. -/
theorem no_positive_ultimate_difference {Q : Type} (g : Magnitudes Q)
    (gap : Nat → Q) (D : Q)
    (hsmall : Exhaustion.VanishingDifference g gap)
    (hterminal : Exhaustion.TerminalLower g gap D) : ¬ g.positive D :=
  Exhaustion.no_positive_terminal g gap D hsmall hterminal

/-- This theorem explicitly restricts the approach to before the finite
endpoint. A zero or negative duration cannot provide a contradiction witness. -/
theorem finite_time_before_end_exhaustion {Q : Type} (g : Magnitudes Q) (T : Q)
    (hT : g.positive T) (gap : Q → Q) (D : Q)
    (hsmall : ∀ d, g.positive d → Exhaustion.BeforeEnd g T (fun h => g.lt (gap h) d))
    (hterminal : ∀ d, g.positive d → g.lt d D →
      Exhaustion.BeforeEnd g T (fun h => g.lt d (gap h))) : ¬ g.positive D :=
  Exhaustion.no_positive_terminal_before_end g T hT gap D hsmall hterminal

theorem ultimate_difference_zero (gap : Nat → Fraction) (D : Fraction)
    (hD : 0 ≤ D.num)
    (hsmall : Exhaustion.VanishingDifference Fraction.magnitudes gap)
    (hterminal : Exhaustion.TerminalLower Fraction.magnitudes gap D) :
    Fraction.equiv D (Fraction.ofInt 0) := by
  have hn := no_positive_ultimate_difference Fraction.magnitudes gap D hsmall hterminal
  have hz : D.num = 0 := by change ¬ 0 < D.num at hn; omega
  simp only [Fraction.equiv, Fraction.ofInt, Int.mul_one, Int.zero_mul, hz]

end Principia1713.LemmaI

/-! De Motu NATP00090: the unnumbered exhaustion step inside Lemma 2.
This is an earlier enclosing-ratio argument, not a De Motu "Lemma I" on
ultimate equality. Lemma 1 in this witness is motion composition.
Witness: NATP00090, 'De motu sphæricorum corporum in fluidis', 40r (statement), 41r (proof).
Source: docs/m1/NATP00090.xml
SHA-256: 790b468987fd8c7716d9d43197ec3a724f7f581ec8b6ed3998edc191b951f998
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par13
Anchor URLs: NATP00090.par12 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par12; NATP00090.par13 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par13
Status: editorial_interpretation; confidence high for the enclosing-ratio
step, not an assertion of an explicit dependence on the later printed Lemma I.
Proof-step correspondence: "ultimis illis intermedia" is represented by
ordered enclosure between two supplied ultimate ratios. The squeeze is proved;
the tangent-area geometry, its limiting premises and the mechanical
quadratic-time assertion are not discharged by this theorem.
-/
/- LATIN BEGIN NATP00090.par12
Lemma 2 Spatium quod corpus urgente quacun vi centripeta ipso motus initio describit, esse in duplicata ratione temporis.
LATIN END NATP00090.par12 -/
/- LATIN BEGIN NATP00090.par13
Exponantur tempora per lineas AB, AD datis Ab Ad proportionales, et urgente vi centripeta æquabili exponentur spat[del: a][add: i]a descripta pea areas rectilineas ABF ADH perpendiculis BF, DH et rectâ quavis AFH terminatas ut exposuit Galilæus. [del: Sit] [add: Vrgente] autem vi[del: s] centripeta inæquabili[del: s et perinde] exponantur spatia descripta per areas ABC, ADE curva quavis ACE quam recta AFH tangit in A, comprehensas. Age rectam AE parallelis BF, bf, dh occurrentem in G, g, e, et ipsis bf, dh occurrat AFH producta in f et h. Quoniam area ABC major est area ABF minor area ABG et area curviline[del: [unclear: ]][add: a] ADEC major area ADH minor area ADEG erit area ABC ad aream ADEG major quam area ABF ad aream ADE[del: F][add: G] minor quam area ABG ad aream ADH hoc est major quam area Abf ad aream Ade minor quam area Abg ad aream Adh. Diminuantur jam lineæ AB, AD in ratione sua data us dum puncta ABD coeunt et linea Ae conveniet cum tangente Ah, adeo ultimæ rationes Abf ad Ade et Abg ad Adh evadent eædem cum ratione Abf ad Adh. Sed hæc ratio est dupla rationis A[add: b][del: [unclear: ]] ad Ad seu AB ad AD ergo ratio ABC ad ADEC ultimis illis intermedia jam fit dupla rationis AB ad AD id est ratio ultima evanescentium spatiorum seu prima nascentium dupla est rationis temporum.
LATIN END NATP00090.par13 -/

namespace DeMotu1684.Exhaustion
open NewtonLimitDynamics

/-- The local enclosing-ratio step uses only elementary ordered exhaustion.
No theorem from either printed Principia edition is used. -/
theorem natp00090_enclosing_ratio_reconstruction {Q : Type} (g : Magnitudes Q)
    (ratio lower upper : Q → Q) (c : Q)
    (hl : Ultimate g lower c) (hu : Ultimate g upper c)
    (hgeometry : Near g (fun h => g.le (lower h) (ratio h) ∧ g.le (ratio h) (upper h))) :
    Ultimate g ratio c :=
  enclosure_reconstruction g ratio lower upper c hl hu hgeometry

end DeMotu1684.Exhaustion

/-! NATP00089 remains separate. Its Theorem 1 has an unnumbered limiting
assertion at par9, preserved with the full Latin in Historical/AreaLaw.lean:
https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par9
That witness does not state the general printed Lemma I or the preceding
NATP00090 Lemma 2 proof. No numbered limiting lemma or new source dependency
is retroactively attributed to NATP00089. -/
