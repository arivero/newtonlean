import NewtonLimitDynamics.Historical.LemmaX.CorollaryII

/-! Historical result: lemma_x_corollary_iii.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1713. Any space under any finite force, as force and square of time jointly. -/
/-! Witness: 1713.
Source: docs/m1/NATP00082.xml
SHA-256: 4a288b47da21c70b46f02e74092c8c16b3f1e7d301a2f04169439a767b949d0c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par32
Anchor URLs: NATP00082.par32 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par32
Proof-step correspondence: "Idem intelligendum est": the edition's Corollary 2 normalization is applied to an arbitrary space `s` described under the force `f`, whose Lemma X coefficient `k * f` is supplied as in Corollary 2. At the beginning of motion the space divided by the force and the square of the time is ultimately `k`.
Historical dependency ledger for this exact witness:
- P1713.L10C2 → P1713.L10C3; passage NATP00082.par32 ("Idem intelligendum est"); witness De Motu Corporum (Liber Primus) (1713); URL https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par32; status explicit_dependency; confidence high.
-/
/- LATIN BEGIN NATP00082.par32
Corol. 3. Idem intelligendum est de spatiis quibusvis quæ corpora urgentibus diversis viribus describunt. Hæc sunt, ipso motus initio, ut vires & quadrata temporum conjunctim.
LATIN END NATP00082.par32 -/

namespace Principia1713.LemmaX
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

/-- A space described under the force `f`, with Lemma X coefficient `k * f`,
is at the beginning of motion as the force and the square of the time jointly:
divided by both it is ultimately the positive calibration `k`. -/
theorem corollary3_spaces_jointly (s : Fraction → Fraction) (k f : Fraction)
    (hk : positive k) (hf : positive f)
    (p : Principia1713.LemmaXPremises magnitudes (ratio s) (mul k f)) :
    QuadraticInitialDeflection magnitudes (fun t => quotient (ratio s t) f hf) k :=
  corollary2_error_normalized s k f hk hf p

end Principia1713.LemmaX
