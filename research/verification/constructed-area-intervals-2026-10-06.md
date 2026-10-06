# Constructed swept-area intervals, 6 October 2026

## Target and permitted premises

Extend the existing general local constructed-curve area law to every pair of
times in its BinaryTime domain. Construct interval area from the actual
curve-node fan between the smaller and larger dyadic tick counts. Prove that
these fans converge to unsigned swept area
`abs(ell) * abs(t1 - t0) / 2`, with address independence, including equal
times and aliases. Prove finite fan composition before using prefix differences.
Equal elapsed time lengths must give equal areas. The between-path enclosure
and vanishing proof remain the existing derived results.

MAY ASSUME: the regional Lipschitz and calibrated-window Conditions; the
existing constructed curve and vertex remainder estimates; proved finite
triangle/fan bounds, Cauchy completion, BinaryLift and GeometricApproximation.
MUST NOT ASSUME: interval area convergence, its desired formula, or an area
enclosure. No new force instance, ODE theorem, mathlib, sorry or new axiom.
Ordinary sector-union content and the full historical limiting passage remain
open; fans count multiplicity. No score change is licensed by this extension.

## Source route

The actual archived TEI proof paragraphs were opened in this session:
1687 NATP00077 par45 and 1713 NATP00082 par51 explicitly add triangle areas
using `componendo` and compare their description times. The two witnesses have
separate URLs and remain separate modern reconstructions:

- https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45
- https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51

De Motu NATP00089 par9 and NATP00090 par17 assert equal areas in equal times
and then infinitely many infinitely small triangles. Neither contains the
printed editions' explicit `componendo` sentence. Interval composition there
is a separately named modern consequence, without a later limiting citation:

- https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par9
- https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par17

The same-session source read also opened the printed proofs of Lemmas I–III
and III Corollary 4 (1687 par2/4/6/10; 1713 par3/5/7/11). Those passages
justify the existing source dependency map; the interval extension does not
certify their historical geometric invocation.

## Load-bearing source extracts

These quotations were copied from the archived TEI proof paragraphs.

[NATP00077 par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45):

> Æqualibus igitur temporibus æquales areæ in plano immoto describuntur: & componendo, sunt arearum summæ quævis SADS, SAFS inter se, ut sunt tempora descriptionum.

[NATP00082 par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51):

> Æqualibus igitur temporibus æquales areæ in plano immoto describuntur: & componendo, sunt arearum summæ quævis SADS, SAFS inter se, ut sunt tempora descriptionum.

## Reuse decision and exact controls

PolygonFanArea and FanValues already construct rational and completed fans,
and SweptArea.AreaAt handles initial-time prefixes, but none defines fans on
an arbitrary interval. Extend those canonical modules and reuse BinaryLift
and GeometricApproximation rather than rebuild any completion operation.

Pre-registered controls: the cyclic points (1,0), (0,1), (-1,0), (0,-1),
(1,0) have unsigned doubled fan 4 and doubled fan 2 on the middle two cells;
zero-length intervals give 0. The points (1,0), (0,1), (1,0) have signed fan
0 and unsigned doubled fan 2. A control equating those two fans must fail.
Reverse endpoint order must preserve unsigned interval area. Binary aliases
and the T=0 domain must remain valid without positive elapsed-time premises.

## Execution and verification

The sequential gpt-6-sol worker compiled the finite controls, canonical
interval fans and actual curve-node estimates, then reached its model usage
limit. Root Sol 6.1 completed the integration: generic tick/time operations
moved into existing foundation modules, address independence precedes the
actual fan-name quotient lift, and the elapsed-time formula is derived.
Root also proved completed fan composition, zero intervals and the four
stage/witness wrappers. No prior public signature changes.

One independent sequential gpt-6-luna verifier ran all 16 README checklist
commands and the scope harness; every command exited 0. Logs:
`/tmp/newton-sol61-interval-final-01.log` through `-16.log` and
`/tmp/newton-sol61-interval-scope-final.log`. API audit:
`/tmp/newton-sol61-interval-api.json`; all 2,093 prior public names and their
signatures remain, with 44 additions. The catalogue has 1,650 theorem rows
and emits 1,506 reference checks. The graph retains 82 nodes, 75 edges and
253 passages. Only propext, Classical.choice and Quot.sound occur. Packages
remain empty, there is no Newton import in BarrowLib, and no sorry/admit,
new axiom or mathlib is used. Cyclic and opposite-orientation controls,
address aliases, zero T and equal/reversed endpoints compile. The completion
scores remain unchanged. The graph PDF's original date metadata was preserved
after its remaining bytes matched HEAD. Conversation exports are excluded.

The proof protocol follows the user's sequential v6 policy; no parallel proof
tournament or protocol grade VERIFIED-CLOSED is claimed. Acceptance here is
Lean kernel compilation, scope review and the full repository checklist.

The next task follows the user's 6 October direction: prove the Laws'
Corollary 1 and Lemma III Corollary 4 through their own source-local proof
dependencies, before a force-specific application. These interval results do
not certify those historical proofs.
