import BarrowLib.Common.RationalMagnitudes
import NewtonLimitDynamics.Historical.LemmaX.CorollaryIII

/-! Historical result: lemma_x_corollary_iv.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1713. Exact coefficient algebra; finite-time force law remains an explicit premise. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par33
Anchor URLs: NATP00082.par33 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par33
Proof-step correspondence: The checked coefficient identity below expresses the ratio algebra; the physical force law is still an explicit premise. The ultimate form applies this edition's Corollary 3 theorem and multiplies by `f / k`: at the beginning of motion the space divided by the calibration `k` and the square of the time is ultimately the force `f`.
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

namespace Principia1713.LemmaX
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

/-- "Ideoque": from Corollary 3, the force is ultimately the space described at
the beginning of motion divided by the calibration and the square of the time. -/
theorem corollary4_from_corollary3 (s : Fraction → Fraction) (k f : Fraction)
    (hk : positive k) (hf : positive f)
    (p : Principia1713.LemmaXPremises magnitudes (ratio s) (mul k f)) :
    Ultimate magnitudes (fun t => quotient (ratio s t) k hk) f := by
  have hm : positive (quotient f k hk) := Int.mul_pos hf k.den_pos
  refine ultimate_target_congr
    (ultimate_congr _ (fun t => mul (quotient f k hk) (quotient (ratio s t) f hf)) _ ?_
      (ultimate_scale (quotient f k hk) hm (corollary3_spaces_jointly s k f hk hf p).2)) ?_
  · intro t _
    unfold equiv quotient mul
    dsimp only
    ac_rfl
  · unfold equiv quotient mul
    dsimp only
    ac_rfl

end Principia1713.LemmaX
