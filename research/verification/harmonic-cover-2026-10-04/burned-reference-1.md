# Harmonic exact holdout provenance

## Birth record, before project comparison

- Fixed source commit: `15d50adda7b8dfeec809559bef785f173d11e017`.
- Birth: 2026-10-04 08:46:45 Europe/Madrid.
- Generator: `/tmp/newtonlean-harmonic-holdout-15d50ad-standalone.lean`; SHA-256 `a0de72d2c4912230b25ed5c64edb4aca3f46dc9239bdc0db055d0eadebb1a43f`.
- Runtime: Lean 4.19.0, commit `6caaee842e94`, importing `Std` only. No project recurrence, norm, determinant, fraction, cover, or library code is imported or called.
- Input fixed before comparison: signed `w=-3/4`, `h=1/30`, three common blocks; initial `x=(2/3,-3/5)`, `v=(-1/4,5/6)`. Common input denominator 60 gives `(x1,x2,v1,v2)=(40,-36,-15,50)`. Coarse uses three durations `2h=1/15`; fine uses six durations `h=1/30`.
- Exact small-time check: `T=6/30`, `1+|w|=7/4`; `2*(6*7)=84 <= 30*4=120`, so `T*(1+|w|) <= 1/2` holds strictly.
- Generator output log: `/tmp/newtonlean-harmonic-holdout-15d50ad-output.log`; SHA-256 `314c17716019b36011376c7a660229472371d52b8bfb33005953cc3e3da5031d`.
- Exact common-denominator trace states use `(den; x1,x2,v1,v2)`:
  - coarse 0: `(60; 40,-36,-15,50)`
  - coarse 1: `(54000; 35100,-29400,-11745,43530)`
  - coarse 2: `(48600000; 30885300,-23848200,-9026235,37984590)`
  - coarse 3: `(43740000000; 27255195900,-19184304600,-6760851705,33226915770)`
  - fine 0: `(60; 40,-36,-15,50)`
  - fine 1: `(216000; 142200,-123600,-50445,176910)`
  - fine 2: `(777600000; 505866600,-423730800,-168955335,626282730)`
  - fine 3: `(2799360000000; 1800845119800,-1450276952400,-563218078005,2218360904190)`
  - fine 4: `(10077696000000000; 6415456261919400,-4954793720137200,-1867198674270015,7862229412080570)`
  - fine 5: `(36279705600000000000; 22871578701997438200,-16893789863044251600,-6150125759822118045,27881681136913945710)`
  - fine 6: `(130606940160000000000000; 81599668236012123354600,-57471841770529632274800,-20100461029459321878135,98937256048626963749130)`
- Exact final state L1 error numerator/denominator after cross multiplication: `33636993566171473893384900000000 / 5712747562598400000000000000000000`.
- Exact cover radius numerator/denominator: `75294/216000`.
- Exact three-block square-cover budget numerator/denominator: `68030237232/46656000000`.
- Accuracy: exact integer arithmetic and common-denominator recurrence; no floating-point approximation or digit claim.
- Predeclared failure criterion: reject any mismatched cross-multiplied project coordinate, state-error, radius, or budget equality; also reject if a deliberately corrupted comparator succeeds.

## Contact log

- At birth, this reference has not been compared with the project and has not informed a code change or tuning choice.
- First comparison: pending. Fixed project source commit remains `15d50adda7b8dfeec809559bef785f173d11e017`.

- First project contact scheduled/recorded before execution: 2026-10-04 08:48:02 Europe/Madrid, against frozen commit `15d50adda7b8dfeec809559bef785f173d11e017`.
- Comparator: `/tmp/newtonlean-harmonic-holdout-15d50ad-project-comparator.lean`; SHA-256 `aec006d5bc9628addb4cd3b4bfc563ae4612e5375270c8dd3434eaf949343ef1`.
- The reference remains unexposed to development/tuning; this is the first exact comparison. Predetermined mismatch/corruption rejection criterion remains as above.
- 2026-10-04 08:48:02 comparator attempt (SHA above) failed as a comparator harness before any comparison completed: the first draft left point/namespaces unresolved and Lean's reducible `decide` did not finish two Fraction equivalence goals. No reference-derived value or change to the project was made; the holdout input/output and production snapshot are unchanged.
- Revised comparator prepared before execution: `/tmp/newtonlean-harmonic-holdout-15d50ad-project-comparator.lean`, SHA-256 `083073342ab9cc5fb63f5a5934706f51383dd8697d79a4307ba39b119c085194`. It raises scratch-file reduction limits and explicitly unfolds no project implementation; all verdicts remain exact Lean equivalence checks.
- 2026-10-04 08:48:55 revised comparator attempt (SHA `083073342ab9cc5fb63f5a5934706f51383dd8697d79a4307ba39b119c085194`) also failed before an exact comparison: the generic Fraction constructor lacked a proof that its denominator was positive; two later reference-state calls still lacked that witness; namespace imports omitted the `stateSub`/threshold definitions. No project change or reference-derived tuning occurred.
- Next comparator prepared before execution at 2026-10-04 08:50:11 Europe/Madrid: same path, SHA-256 `426e9cb899dbbd4697f02281b8ae24a3f9db8f42749e827879f5e4b6fcfae956`; it supplies explicit positive-denominator witnesses and required namespaces. The holdout data remain fixed.
- Final first-reference comparator contact at 08:51:03, comparator SHA `0a7bda8c89dce92b30c57d22d37a8862df64073e017104c39bbaaa8f9bbb47ef`; output `/tmp/newtonlean-harmonic-holdout-15d50ad-comparison.log`, SHA-256 `6ced7bba9cc1e82f2fb4578796fbbe67ef1ec8e788c7153686027a5e87957a50`. It was invalid: project `fineAt n` is a two-half-cell block recursion, but this comparator still compared half-step indices n. The reference is burned for comparator debugging; it is not used as certification evidence.
