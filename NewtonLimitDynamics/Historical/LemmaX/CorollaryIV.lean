import BarrowLib.Common.RationalMagnitudes

/-! Historical result: lemma_x_corollary_iv.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1713. Exact coefficient algebra; finite-time force law remains an explicit premise. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par33
Anchor URLs: NATP00082.par33 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par33
Proof-step correspondence: The checked coefficient identity below expresses the ratio algebra; the physical force law is still an explicit premise.
Historical dependency ledger for this exact witness:
- P1713.L10C3 → P1713.L10C4; passage NATP00082.par33; witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par33; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par33
Corol. 4. Ideoque vires sunt ut spatia, ipso motus initio, descripta directe & quadrata temporum inverse.
LATIN END NATP00082.par33 -/

namespace Principia1713
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

theorem corollary4_coefficient_reconstruction (k f t : Fraction)
    (hk : positive k) (ht : positive t) :
    equiv (quotient (generated k f t) (mul k (mul t t))
      (positive_mul k _ hk (positive_mul t t ht ht))) f := by
  unfold equiv quotient generated mul
  dsimp
  ac_rfl

end Principia1713
