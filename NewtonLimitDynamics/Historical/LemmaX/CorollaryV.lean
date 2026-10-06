import BarrowLib.Common.RationalMagnitudes

/-! Historical result: lemma_x_corollary_v.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1713. Exact coefficient algebra with positive force; finite-time law remains an explicit premise. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par34
Anchor URLs: NATP00082.par34 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par34
Proof-step correspondence: The checked coefficient identity below expresses the ratio algebra; the physical force law is still an explicit premise.
-/
/- LATIN BEGIN NATP00082.par34
Corol. 5. Et quadrata temporum sunt ut descripta spatia directe & vires inverse.
LATIN END NATP00082.par34 -/

namespace Principia1713
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

theorem corollary5_coefficient_reconstruction (k f t : Fraction)
    (hk : positive k) (hf : positive f) :
    equiv (quotient (generated k f t) (mul k f) (positive_mul k f hk hf))
      (mul t t) := by
  unfold equiv quotient generated mul
  dsimp
  ac_rfl

end Principia1713
