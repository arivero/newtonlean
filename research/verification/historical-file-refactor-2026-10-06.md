# Historical-file refactor, 6 October 2026

Review state: the Lean refactor is executed in the working tree and deliberately uncommitted for
the user's ultracorrection tool. New refactor files are staged at the user's
request; existing tracked-file changes remain unstaged. Review the complete
change with `git diff HEAD`. Baseline and HEAD at verification: `9f3ec58`.
The user subsequently authorized a Markdown-only commit; this does not release
the remaining code/artifact review hold. Staging counts below describe the
verification checkpoint before that documentation commit.

## Latest review corrections

One file per historical result under `NewtonLimitDynamics/Historical`, with
separate witness sections. The 19 files contain 40 witness sections and 67
source-checked paragraph anchors. Exact diplomatic statement/proof text comes
from archived Newton Project TEI: orig rather than reg, collapsed whitespace,
marked additions/deletions/notes/unclear, and omitted `fw` forme-work.

The shared renderer now drops catchwords and page furniture, preserving
following body text. Regeneration removes NATP00090 par17's duplicated
`describens42 describens`. The source-faithful 1713 reading `Ipsi S BS` is
retained. All archived TEI hashes remain unchanged. Known-answer controls
cover nested forme-work and both actual passages.

Each historical file can contain primary proofs using BarrowLib/ClassicsLib,
followed by an anachronical section using ModernLib, separated by exactly
five full lines of `=` characters and `ANACHRONICAL PROOFS`. Edition-specific
modern area wrappers now live in that section of AreaLaw. Elementary
historical wrappers returned to their result files; finite dependencies
moved into the elementary/classical libraries. Generic post-Newtonian
constructions and diagnostics remain in ModernLib.

Lemma I/II namespaces now match their files. The two combined-result theorem
families moved to generic ModernLib reconstruction namespaces. Nine deliberate
renames are recorded in [declaration-renames.json](../declaration-renames.json);
no aliases or duplicate public theorems were added to preserve incorrect names.
The [module migration map](../module-migration.json) records changed imports.
The final inventory is 39 BarrowLib, three ClassicsLib, 109 ModernLib and
19 historical implementation modules, plus four roots: 174 Lean files.

## Compiled proof provenance and remaining gap

The manifest partitions 43 historical declarations into 25 primary and
18 anachronical declarations. These counts include definitions and partial
results; they do not count completed Newton proofs.

[proof-dependencies.json](../proof-dependencies.json) records 6,335 compiled
project constants and checks types and stored proof/definition bodies,
including private/generated constants. ModernLib constants and explicitly
anachronical declarations seed taint; all downstream uses inherit it,
including uses across files. The 25 primary declarations have no detected
taint. Imports alone do not decide the status of a declaration.

The source-evidence graph is distinct from this compiled graph. No cross-file
use of a manifested historical declaration is currently detected. Of its
75 source-evidenced proof dependencies, 26 have a source result outside these
files, 41 have no primary source formalization, five have no primary target
formalization, and three have no primary declaration use. These are remaining
proof obligations. The partial proofs still use supplied interfaces;
adding unused imports would not derive the interfaces or implement Newton's
cited chain. The ledger preserves exact source evidence and classification
alongside each formal-use status.

No historical theorem was newly completed and completion estimates are
unchanged. Trajectory existence remains a supplied curve, without area,
agreement or convergence built into that premise. Ordinary swept-sector area,
full historical limiting proofs and De Motu antecedent matching for
Propositions II–IV remain open. ClassicsLib proves the existing coordinate
special cases of Euclid I.37/I.38, not their full synthetic geometry.

## Verification

The source/API and compiled-type audits against `9f3ec58` preserve all 2,252
public declarations after applying exactly the nine declared renames. No
normalized statement, proof/definition body or type changed. The earlier
2,253 inventory incorrectly counted `private noncomputable prefixMax` as
public; the reader now has a regression control. The theorem catalogue has
1,735 rows, including private theorems.

The reproducible kernel audit passed:
`python3 scripts/check_migration_api.py --kernel --report research/verification/historical-file-refactor-api-2026-10-06.json`.
The [JSON report](historical-file-refactor-api-2026-10-06.json) records the
rename map, printed-type output hash and raw outputs in `/tmp`. Printed
types are normalized only by the declared renames and joining indented
printer continuation lines. Both isolated baseline and current builds use
Lean 4.19.0 core/Std, with no mathlib.

Architecture controls verify ownership, source identity, exact running Latin,
imports and boundaries. Eight planted corruptions are rejected: catchword
reinjection, missing five-line header, wrong lemma namespace, falsely primary
anachronical declaration, Latin-marker drift, backward import, second result
marker and stale source hash. Dependency controls cover type-only taint,
annotation-only taint through another document, cycles and a compiled private
helper bridge. They do not certify unproved historical premises.

The sequential gpt-6-luna verification of these corrections passed all
16 README checks: default, BarrowLib and NewtonLimitDynamics builds; both
catalogues; source collation; graph validation; edition comparison; graph and
progress regeneration; Lean reference/axiom inspection; declaration-reader,
evidence-validation and graph-rendering controls; source hashes; whitespace.
Logs: `/tmp/newton-refactor-review-fixes-01.log` through `-16.log`.

Checks 17–21 passed ClassicsLib and ModernLib builds, architecture, its eight
negative controls and source/API comparison. Seven existing Lean harnesses
passed at logs 22–28, in order: given-trajectory consistency; trajectory
postulate; constructed-area intervals; Laws Corollary I; Lemma III chord
boundaries; Lemma III supporting boundaries; Lemmas II–III rectangles.
All are the corresponding dated files under `research/verification/`.
Reference inspection reports only `propext`, `Classical.choice`, `Quot.sound`,
with no project axiom or `sorryAx`.

The compiled dependency check and its controls also passed; logs are
`/tmp/newton-refactor-review-fixes-check-proof-layers.log` and
`/tmp/newton-refactor-review-fixes-test-proof-layers.log`. The earlier
verification checkpoint used `/tmp/newton-refactor-final-01.log` through
`-28.log`. Refreshing the index exposed trailing blank lines in two new reconstruction
files; those lines were removed. The affected ModernLib/NewtonLimitDynamics
builds, default build, architecture, source/API and compiled dependency checks
then passed again (post-staging logs
`/tmp/newton-refactor-review-poststage-01.log` through `-04.log`). The reading
artifact was regenerated again. Both staged and complete-tree whitespace
checks pass; 154 new files are staged with their latest contents. Existing
tracked edits remain unstaged. The unrelated conversation export is excluded.
No commit or push occurred; HEAD remains `9f3ec58`.

## Reading artifact

`python3 scripts/principia_lean_interleave.py WORKTREE` regenerated the
paired Markdown from the current layout. Coverage comparison confirms all
174 library files appear verbatim exactly once. Pandoc/XeLaTeX regenerated
the 433-page PDF; `pdfinfo` and `qpdf --check` passed. A rendered page was
inspected, including the five-line anachronical separator on page 149.
Build log: `/tmp/newton-refactor-review-reading-pdf.log`.

The PDF is a reading aid: no installed font supplies Newton Project's
private-use U+E8BF glyph. XeLaTeX reports that limitation. The exact character
remains in source-checked Lean and Markdown, without silent replacement in
the Latin.
