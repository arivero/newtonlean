# Project method

- Current review hold: the 6 October historical-file refactor is deliberately
  uncommitted at the user's request. Do not commit or push it before the user
  releases the hold after their ultracorrection review.
  Markdown and obsolete-path deletions were committed at the user's request.
  The remaining refactor still needs review before commit or push. The user
  separately authorized removing all JSON bookkeeping and its Python tools.

- User-selected refactor direction, 6 October: one file per historical result,
  with separate edition/witness sections in that file. Each section contains
  its exact Latin statement and proof, then the corresponding definitions
  and checked formalization. Keep different Newton stages and De Motu witness
  revisions explicit; sharing a file does not merge their premises. Supporting
  mathematics belongs in BarrowLib (elementary), ClassicsLib (source-identified
  classical results, e.g. Euclid), or ModernLib (post-Newtonian concepts).
  See research/HISTORICAL_FILE_REFACTOR.md for the approved layout and executed
  migration. The old placement of modern Cauchy machinery in BarrowLib is to
  be revised; do not count relocation as mathematical proof progress.

- User clarification, 6 October: primary Newton proofs may use BarrowLib,
  ClassicsLib and other primary historical results. Anachronical proofs may
  occupy a separate section of the same result file and use ModernLib.
  Separate that section with a comment header containing exactly five full
  lines of `=` characters, followed by `ANACHRONICAL PROOFS`. Using an
  anachronical result taints every downstream proof, including uses through
  other files, private helpers or types. File imports alone do not classify
  a proof. Inspect compiled dependencies with
  `lake env lean research/CheckReferences.lean`; source dependency comments
  alone do not establish formal use or discharge supplied interfaces.

- User clarification, 6 October: the primary historical proof takes the
  trajectory's existence as an explicit postulate, represented in Lean by
  the supplied curve parameter. Do not require a new trajectory-existence
  construction before proving Proposition I. Its goal is (A) swept sector
  areas proportional to time. The separate (B) nonnegative area between the
  given curve and Newton's polygon is an approximation control to be proved.
  Neither (A), (B), nor polygon/curve agreement belongs in the existence
  postulate. Retain completed constructive results as supporting work.
  This convention is user-authorized interpretation, not a new quotation or
  explicit historical axiom attributed to Newton. Ordinary Lean proofs still
  have no sorry or undeclared axioms; a given curve is an explicit premise.

- User direction, 6 October: no JSON source catalogs, proof ledgers, migration
  manifests or bookkeeping schemas, and no Python tools managing them. Use
  Git for history, Markdown for maintained research evidence/status, and the
  historical Lean files for exact Latin and proof correspondence. Do not
  replace the removed layer with an equivalent tracking format. Lake's own
  dependency lockfile is build metadata and is retained.
  Obsolete generated graphs, source indexes and docs/m1 Markdown stubs are
  removed too. Recover graphs from current Lean source and compiled dependencies
  with `lake env lean scripts/inspect_graphs.lean`; distinguish source evidence,
  imports and actual formal uses. Keep the archived originals and their hashes.

- Work source-first. Preserve Newton's textual stages separately; never merge
  *De Motu*, 1687, proposed 1694, 1713, or 1726 claims silently.
- For every historical edge record the exact passage, witness, URL, status
  (`explicit_dependency`, `implicit_dependency`, `modern_reconstruction`, or
  `editorial_interpretation`), and confidence.
- A source that merely places one result after another does not establish a
  proof dependency. Historical Lean theorems must be named separately from
  modern consequences.
- The approved programme is Book I, Section II, Propositions I–IV in
  De Motu (corresponding arguments, without retrospective numbering), 1687,
  and 1713. See research/GOALS.md. Proposed 1694 and 1726 are supporting
  comparisons. M1–M4 remain supporting work, not certified complete proofs.
- Keep the boundary/action-constant hypothesis in a separate diagnostic layer.
  Do not use quantum or later mechanical premises to close historical proofs;
  a failed tactic does not establish a mathematical obstruction.
- Prefer normalized and diplomatic Newton Project transcriptions, with TEI/XML
  as the machine-readable authority where available.
- Do not claim a Lean proof until it compiles with the declared Lean/mathlib
  version. The current environment may lack Lean; record that fact explicitly.
- M1 uses Lean core only. Do not download mathlib or use post-Newtonian
  theorems to fill historical proof gaps. Ratios, geometric constructions,
  and limiting premises must be explicit; name conditional reconstructions
  honestly. Any later dependency expansion requires reconsideration with the user.
- Use `lake build NewtonLimitDynamics` as well as the default build. A successful
  command that does not compile the library is not proof verification.
- Build the elementary foundation explicitly with `lake build BarrowLib` too.
- Preserve unrelated conversation-export edits and avoid full cache downloads.
- Use v6 models for all new delegated work: `gpt-6-sol` for bounded reasoning
  and technical implementation, `gpt-6-luna` for routine verification and
  compilation. This supersedes earlier 5.5/5.6 model assignments and the
  previous Terra implementation assignment; no v6 Terra is currently exposed.
  Do not silently fall back to a v5 model. Run at most one
  subagent at a time, with concise reports; no Astra subagents. This is the
  user's approved resource policy. Do not launch parallel agent work.
- User-authorized handoff exception: the next bounded task and its commit are
  assigned to the upgraded Claude Code. This supersedes the old handoff's
  prohibition on Claude for that task. Claude Code may implement and verify
  the task itself; the Codex-specific model assignments above do not prevent
  this handoff. Keep execution sequential and all proof/source constraints.
- Current handoff: research/HANDOFF-2026-10-06-REWORKED-SOURCES.md.
  The user retired the 4 October handoff as an execution plan after the
  source refactor and bookkeeping cleanup. Preserve its results, but follow
  the new source-local proof order and carried-forward obligations. The
  exception above covered the 22 September session's tasks, which are complete.
