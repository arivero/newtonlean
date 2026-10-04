# Harmonic exact holdout 3 provenance

## Birth record, before project comparison

- Fixed source commit: `15d50adda7b8dfeec809559bef785f173d11e017`.
- Birth: 2026-10-04 08:55:10 Europe/Madrid.
- Generator: `/tmp/newtonlean-harmonic-holdout3-15d50ad-standalone.lean`; SHA-256 `22b636f63e21303fb3647cc01abe13c5a72c6ba0372a432bf123bc61b0e41f68`.
- Runtime: Lean 4.19.0, commit `6caaee842e94`, importing `Std` only. It uses a hand-written exact common-denominator integer recurrence; no project cell, norm, determinant, Fraction, schedule, or cover functions are imported or called.
- Input fixed before comparison: signed `w=-2/3`, `h=1/24`, two coarse blocks; `x=(-2/5,3/7)`, `v=(4/9,-5/8)`. Common initial denominator 2520 gives `(-1008,1080,1120,-1575)`. Coarse cells have duration `2h=1/12`; fine has four cells of duration `h=1/24`.
- Small-time check: `T=4/24`, `1+|w|=5/3`; `2*(4*5)=40 < 24*3=72`, so the condition is strictly satisfied.
- Generator output: `/tmp/newtonlean-harmonic-holdout3-15d50ad-output.log`; SHA-256 `c722b1ecf1088fb84c7828ddee4145d16702ec0108b24ecd4adf1f1fcb2140e4`.
- Exact states `(den; x1,x2,v1,v2)`:
  - coarse 0: `(2520; -1008,1080,1120,-1575)`
  - coarse 1: `(1088640; -395136,409860,461888,-657630)`
  - coarse 2: `(470292480; -154070784,153384840,190976128,-275574780)`
  - fine 0: `(2520; -1008,1080,1120,-1575)`
  - fine 1: `(4354560; -1661184,1752840,1889216,-2672910)`
  - fine 2: `(7524679680; -2734502400,2836458000,3188606848,-4539997980)`
  - fine 3: `(13002646487040; -4495640454144,4574519569440,5385033731840,-7718046521400)`
  - fine 4: `(22468573129605120; -7380744276068352,7349070466451520,9100317614284288,-13132643542688880)`
- Exact final state L1 error numerator/denominator after common-denominator cross multiplication: `45970688072946954240000 / 10566800979183353305497600`.
- Exact radius: `1492296/4354560`.
- Exact two-block cover budget: `17815578812928/18962192793600`.
- Accuracy is exact integer arithmetic, with no floating-point approximation or digit claim.
- Failure criterion fixed before comparison: any cross-multiplied mismatch in all coarse/fine block coordinates, final state L1 error, radius, or budget is failure; a deliberately corrupted comparator must also fail.

## Contact log

- At birth this reference has not contacted project output, code tuning, or repair.
- First project contact: pending; project commit fixed at `15d50adda7b8dfeec809559bef785f173d11e017`.
- First project contact scheduled and recorded before execution: 2026-10-04 08:55:51 Europe/Madrid, fixed commit `15d50adda7b8dfeec809559bef785f173d11e017`.
- Comparator: `/tmp/newtonlean-harmonic-holdout3-15d50ad-project-comparator.lean`; SHA-256 `793a0a555306bf2b3b103f72ca805a078ad7f58600ea18fa1b938d2cb1d34f52`.
- Comparator uses block indices: each fine block is two standalone half-cell updates; fineAt indices 0–2 compare with reference trace entries 0, 2, 4. The fixed failure criterion above applies.
- Corruption control prepared before running: 2026-10-04 08:56:19 Europe/Madrid, file `/tmp/newtonlean-harmonic-holdout3-15d50ad-corrupted-comparator.lean`, SHA-256 `c4bc9525d5f2b06aac87c3fa7fc76bfd5977301fd5faefe02413c209798ce470`. It adds 1 to the standalone cover-radius numerator; expected outcome is Lean rejection.
- The first corruption-control attempt on the above file hash did fail Lean, but due an unresolved `Point` alias and reduction not reaching the false equality; this was a broken negative harness, not evidence. Corrected scratch comparator prepared before rerun at 2026-10-04 08:56:33 Europe/Madrid: same path, SHA-256 `198e4150d08b9246ae4921a20d33e94757c4dc27148c60a837bb730db97ae728`; imports the proper point namespace and uses the same reduction limits as the passing check.

## Comparison outcome

- At the recorded first contact, all block coordinate and state-error/radius/budget comparisons passed by exact Lean cross multiplication. Output: `/tmp/newtonlean-harmonic-holdout3-15d50ad-comparison.log`; SHA-256 `efccade521543a27f418315c5a1db8b2b6be3f1397707ff2caf5c5b5342a160d`.
- The five comparator theorems reported only `propext`; no `sorryAx` was introduced.
- Corruption control: the radius numerator was increased by 1. After correcting an initial scratch import issue, Lean rejected it specifically because `decide` proved the proposition false. Final control source SHA is recorded above; output `/tmp/newtonlean-harmonic-holdout3-15d50ad-corruption.log`, SHA-256 `8392addbcdeb2407921c1b73ebae02230482c64c14173afc72339def8707346c`.
- No project source was repaired or changed from the frozen commit. This arithmetic check validates finite formulas, block indexing, signs and normalization for the selected case only; it does not independently validate the Lean kernel or prove trajectory existence or a historical limit.
