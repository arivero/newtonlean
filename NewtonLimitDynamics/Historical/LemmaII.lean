import BarrowLib.Polygon.MonotoneRectangles

/-! Historical result: lemma_ii.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Equal-width gap identity in an explicit rational monotone graph model. -/
/-! Witness: 1687.
Source: docs/m1/NATP00077.xml
SHA-256: 57a8eb4ae7307faed09e2ae572a4975ea2011e679ce52e6ad2413028c424dffa
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par3
Anchor URLs: NATP00077.par3 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par3; NATP00077.par4 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par4
Proof-step correspondence: The equal-width inscribed/circumscribed rectangle gap corresponds to the finite equality below; ultimate curvilinear equality remains open.
Historical dependency ledger for this exact witness:
- P1687.L1 → P1687.L2; passage NATP00077.par4; witness De Motu Corporum (Liber Primus) (1687); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par4; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00077.par3
Si in figura quavis Aa cE rectis Aa, AE, & curva AcE comprehensa, inscribentur parallelogramma quotcunq; Ab, Bc, Cd, &c. sub basibus AB, BC, CD, &c. æqualibus, & lateribus Bb, Cc, Dd, &c. figuræ lateri Aa parallelis comenta; & compleantur parallelogramma aKbl, bLcm, cMdn, &c, Dein horum parallelogrammorum latitudo minuatur, & numerus augeatur in infinitum: dico quod ultimæ rationes, quas habent ad se invicem figura inscripta AKbLcMdD, circumscripta AalbmcndoE, & curvilinea AabcdE, sunt rationes æqualitatis.
LATIN END NATP00077.par3 -/
/- LATIN BEGIN NATP00077.par4
Nam figuræ inscriptæ & circumscriptæ differentia est summa parallelogrammorum Kl+Lm+Mn+Do, hoc est (ob æquales omnium bases) rectangulum sub unius basi Kb & altitudinum summa Aa, id est rectangulum ABla. Sed hoc rectangulum, eo quod latitudo ejus AB in infinitum minuitur, sit minus quovis dato. Ergo, per Lemma I, figura inscripta & circumscripta & multo magis figura curvilinea intermedia fiunt ultimo æquales. Q.E.D.
LATIN END NATP00077.par4 -/

namespace Principia1687.LemmaII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

theorem lemma2_equal_width_gap (g : Fraction → Fraction) (a b M : Fraction)
    (p : MonotoneRectangles.Partition a b) (hg : MonotoneRectangles.MonotoneOn g a b)
    (hM : ∀ i, i<p.count → Fraction.equiv (MonotoneRectangles.width p i) M) :
    Fraction.equiv (MonotoneRectangles.gap g p)
      (Fraction.mul M (HarmonicTimeComparison.durationDifference (g a) (g b))) :=
  MonotoneRectangles.gap_equal_width g p hg M hM

end Principia1687.LemmaII

/-! 1713. Equal-width gap identity in an explicit rational monotone graph model. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par4
Anchor URLs: NATP00082.par4 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par4; NATP00082.par5 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par5
Proof-step correspondence: The equal-width inscribed/circumscribed rectangle gap corresponds to the finite equality below; ultimate curvilinear equality remains open.
Historical dependency ledger for this exact witness:
- P1713.L1 → P1713.L2; passage NATP00082.par5; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par5; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par4
Si in Figura quavis AacE rectis Aa, AE, & curva AcE comprehensa, inscribentur parallelogramma quotcunque Ab, Bc, Cd, &c. sub basibus AB, BC, CD, &c. æqualibus, & lateribus Bb, Cc, Dd, &c. Figuræ lateri Aa parallelis comenta; & compleantur parallelogramma aKbl, bLcm, cMdn, &c. Dein horum parallelogrammorum latitudo minuatur, & numerus augeatur in infinitum: dico quod ultimæ rationes, quas habent ad se invicem Figura inscripta AKbLcMdD, circumscripta AalbmcndoE, & curvilinea AabcdE, sunt rationes æqualitatis.
LATIN END NATP00082.par4 -/
/- LATIN BEGIN NATP00082.par5
Nam figuræ inscriptæ & circumscriptæ differentia est summa parallelogrammorum Kl, Lm, Mn, Do, hoc est (ob æquales omnium bases) rectangulum sub unius basi Kb & altitudinum summa Aa, id est rectangulum ABla. Sed hoc rectangulum, eo quod latitudo ejus AB in infinitum minuitur, sit minus quovis dato. Ergo (per Lemma I) Figura inscripta & circumscripta & multo magis Figura curvilinea intermedia fiunt ultimo æquales. Q.E.D.
LATIN END NATP00082.par5 -/

namespace Principia1713.LemmaII
open NewtonLimitDynamics NewtonLimitDynamics.Polygon

theorem lemma2_equal_width_gap (g : Fraction → Fraction) (a b M : Fraction)
    (p : MonotoneRectangles.Partition a b) (hg : MonotoneRectangles.MonotoneOn g a b)
    (hM : ∀ i, i<p.count → Fraction.equiv (MonotoneRectangles.width p i) M) :
    Fraction.equiv (MonotoneRectangles.gap g p)
      (Fraction.mul M (HarmonicTimeComparison.durationDifference (g a) (g b))) :=
  MonotoneRectangles.gap_equal_width g p hg M hM

end Principia1713.LemmaII
