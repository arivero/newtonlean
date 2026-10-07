import BarrowLib.Common.RationalMagnitudes
import NewtonLimitDynamics.Historical.LemmaX.CorollaryIII

/-! Historical result: lemma_x_corollary_v.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1713. Exact coefficient algebra with positive force; finite-time law remains an explicit premise. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par34
Anchor URLs: NATP00082.par34 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par34
Proof-step correspondence: The checked coefficient identity below expresses the ratio algebra; the physical force law is still an explicit premise. The ultimate form applies this edition's Corollary 3 theorem and divides by the calibration `k`: at the beginning of motion the space divided by `k * f` has to the square of the time an ultimate ratio of equality.
Historical dependency ledger for this exact witness:
- P1713.L10C3 → P1713.L10C5; passage NATP00082.par34 (the same proportion solved for the square of the time); witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par34; status implicit_dependency; confidence medium.
- P1713.L10C4 → P1713.L10C5; passage NATP00082.par34 ("Et quadrata temporum" inverts Corollary 4's proportion); witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par34; status implicit_dependency; confidence medium.
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

namespace Principia1713.LemmaX
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

/-- From Corollary 3, the square of the time is ultimately the space described
at the beginning of motion divided by the calibration and the force: their
ratio is ultimately one. -/
theorem corollary5_from_corollary3 (s : Fraction → Fraction) (k f : Fraction)
    (hk : positive k) (hf : positive f)
    (p : Principia1713.LemmaXPremises magnitudes (ratio s) (mul k f)) :
    Ultimate magnitudes (fun t => quotient (ratio s t) (mul k f) (positive_mul k f hk hf))
      (ofInt 1) := by
  refine ultimate_target_congr
    (ultimate_congr _ (fun t => quotient (quotient (ratio s t) f hf) k hk) _ ?_
      (ultimate_quotient k hk (corollary3_spaces_jointly s k f hk hf p).2)) ?_
  · intro t _
    unfold equiv quotient mul
    dsimp only
    ac_rfl
  · unfold equiv quotient ofInt
    dsimp only
    ac_rfl

end Principia1713.LemmaX
