# Harmonic exact holdout 2 provenance

## Birth record, before project comparison

- Fixed source commit: `15d50adda7b8dfeec809559bef785f173d11e017`.
- Birth: 2026-10-04 08:52:06 Europe/Madrid.
- Generator: `/tmp/newtonlean-harmonic-holdout2-15d50ad-standalone.lean`; SHA-256 `6690ca0c731597994da9501f5d725504472cc7a80129de16c9ee36b40c6e6ad0`.
- Runtime: Lean 4.19.0, commit `6caaee842e94`, importing `Std` only. This generator uses a hand-written common-denominator integer recurrence and does not import or call project cell, norm, determinant, fraction, schedule, or cover code.
- Frozen input: signed `w=-5/7`, `h=1/40`, three coarse blocks; initial `x=(2/7,-3/8)`, `v=(5/9,-4/11)`. The common initial denominator 5544 gives `(x1,x2,v1,v2)=(1584,-2079,3080,-2016)`. Coarse duration is `2h=1/20`; fine schedule has six half-cells of duration `h=1/40`.
- Small-time condition: `T=6/40`, `1+|w|=12/7`; the exact cross-multiplied test is `2*(6*12)=144 < 40*7=280`, so `T*(1+|w|)<1/2`.
- Generator output log: `/tmp/newtonlean-harmonic-holdout2-15d50ad-output.log`; SHA-256 `c0520787ed6eb6007eefdaaea440b4283722947c605c24557ee1cea1cf213a7a`.
- Exact states `(den; x1,x2,v1,v2)`:
  - coarse 0: `(5544; 1584,-2079,3080,-2016)`
  - coarse 1: `(4989600; 1610400,-1992060,2852520,-1914003)`
  - coarse 2: `(4490640000; 1620511200,-1907694180,2648293560,-1817987409)`
  - coarse 3: `(4041576000000; 1617357693600,-1826004006540,2464332088680,-1727488868427)`
  - fine 0: `(5544; 1584,-2079,3080,-2016)`
  - fine 1: `(19958400; 6072000,-7726320,11239800,-7450758)`
  - fine 2: `(71850240000; 23207976000,-28708842960,41043479400,-27540449874)`
  - fine 3: `(258660864000000; 88473931128000,-106656688640880,149968374118200,-101812036762422)`
  - fine 4: `(931179110400000000; 336502356954984000,-396181523518658640,548298705749394600,-376427870432685666)`
  - fine 5: `(3352244797440000000000; 1277204329727869752000,-1471424829119093383920,2005805448941017303800,-1391925954285645732198)`
  - fine 6: `(12068081270784000000000000; 4838632240893253183656000,-5464160499343013669975760,7341865422209993623271400,-5147537447911899977662194)`
- Exact final state L1 error numerator/denominator, from cross multiplication: `2843735736804398711149754880000000000000 / 1331768300186694737461248000000000000000000`.
- Exact cover radius numerator/denominator: `10598390/62092800`.
- Exact three-block square-cover budget numerator/denominator: `1347910447105200/3855515811840000`.
- Accuracy: exact integer arithmetic and common-denominator recurrence; no floating-point approximation or digit claim.
- Failure criterion fixed before comparison: any cross-multiplied mismatch in each coarse/fine block state, final state L1 error, radius, or budget is failure; the separately corrupted comparator must fail.

## Contact log

- At birth, this reference has not been compared with project output or used to change/tune project code.
- First project contact: pending. Project commit fixed at `15d50adda7b8dfeec809559bef785f173d11e017`.
- First project contact scheduled/recorded before the check: 2026-10-04 08:53:09 Europe/Madrid, fixed commit `15d50adda7b8dfeec809559bef785f173d11e017`.
- Comparator: `/tmp/newtonlean-harmonic-holdout2-15d50ad-project-comparator.lean`; SHA-256 `475a85843a45d5c321968cb6f7fb2b56b8f0c6e077d330595106ed82cbed7c3a`.
- Fine comparator indices are fixed by the block recursion: each `fineAt` block advances two standalone half-cell updates, so comparator indices 0–3 are checked against standalone trace entries 0, 2, 4, 6. Failure criteria above were fixed before comparison.
- First project contact at 08:53:09 used comparator SHA `475a85843a45d5c321968cb6f7fb2b56b8f0c6e077d330595106ed82cbed7c3a`; output `/tmp/newtonlean-harmonic-holdout2-15d50ad-comparison.log`, SHA-256 `c682fd5875270e63ed5b556d7ff330b1236a6f7a715537616032bcb81089a1ed`. Coarse/fine coordinate assertions failed because the standalone printed traces still used copied parameters for a prior sample, though computed state-error/radius/budget formulas used the newly recorded input. This reference is burned for harness debugging and is not certification evidence.
