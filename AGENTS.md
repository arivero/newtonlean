# Project method

- User decision, 10 October 2026: use Lean 4.34.1, replacing the 4.19.0
  toolchain. Lean core only remains mandatory: no mathlib, Batteries or other
  packages. Core types and lemmas (Nat, Int, Rat, Dyadic, Quotient, List) are
  encoding infrastructure, outside historical dependencies and M/H scores.
  Migrate Fraction to core Rat in verified stages, then review the placement
  of surviving mathematics. Migration and relocation earn no completion
  credit: reassess README percentages in every commit and explicitly retain
  them unchanged for this work. Preserve historical theorem names, meanings,
  exact Latin, edition sections and provenance; stop and report if a
  representative-sensitive statement cannot retain its meaning under Rat.
  User clarification, 10 October: core encoding does not establish historical
  availability. Preserve exact source attestations and their domain limits;
  source-only or alternate Lean files may retain historical statements for
  future verification, without routing existing proofs through them.

- User rule, 8 October: every commit must modify the README completion-
  percentage information. Reassess the affected file/witness estimates as
  work done / (work done + estimated remaining work), and update their
  percentages and remaining-work rationale in the same commit. If a rounded
  percentage remains justified, explicitly record the reassessment and why
  it is unchanged in the README progress section; do not invent progress.
  Refresh the measured lines, theorem counts and dependency sizes when they
  change. Verify the task-owned changes, commit them and push immediately.

- User clarification, 7 October: library chronology is ClassicsLib through
  Hypatia, BarrowLib after Hypatia and before the Principia, and ModernLib
  after the Principia. Keep these scopes at the library entry points. Each
  pre-Principia Chinese result belongs in ClassicsLib by explicit exception;
  Arabic results belong in BarrowLib when their dates fit its window. Every
  library element needs its original-language source; Unicode comments are
  allowed. A cited external source must state the exact result. An unmatched
  AI-derived result may cite its own original statement/proof and claim that
  provenance explicitly, without claiming historical textual support or
  priority. Never attribute a known result to its AI formalizer; unmatched
  sources remain unverified unless the result is actually derived here.
  Its class follows its mathematical dependencies: Classics only
  gives Classics, Barrow plus Classics gives Barrow, any modern use gives
  Modern. New authorship alone does not make a result modern.
- Anachronical proofs carry an opening `Modern dependency score` comment:
  M/(M+H), counting distinct transitive mathematical theorem/axiom
  dependencies, with fewer modern dependencies preferred. Traverse types,
  definitions and private helpers; exclude the proof itself and Lean's
  logical/compiler infrastructure. Report M and H so adding historical
  helpers cannot conceal an unchanged modern burden. The score is not a
  completion percentage or a historical-source certificate.
- For this task the user explicitly authorized the final Astra review after
  reset, overriding the older no-Astra restriction below. Keep all other
  resource limits, including at most one sequential subagent.

- The user released the review hold on 6 October with “push as it is”. The
  verified refactor and source-only cleanup were committed and pushed as
  `60180f2`. Continue with verified increments, preserving unrelated changes.
  State and open obligations live together in research/STATE.md; the current
  verification checklist is research/VERIFICATION.md, not a session log.

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
  The remaining Python/parser, progress plots, whole-library interleaved
  reference and rendered PDFs are removed too. Historical Lean files provide
  the result correspondence; reader Markdown can be rendered on demand.
  Keep only the handoff named below. Retain the Lean verification harnesses;
  superseded handoffs, milestone/session reports and checkpoint notes live
  in Git rather than as a parallel working record.

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
  comparisons. The former M1–M4 milestones remain supporting work, not
  certified complete proofs; their reports are retained in Git.
- Keep the boundary/action-constant hypothesis in a separate diagnostic layer.
  Do not use quantum or later mechanical premises to close historical proofs;
  a failed tactic does not establish a mathematical obstruction.
- Prefer normalized and diplomatic Newton Project transcriptions, with TEI/XML
  as the machine-readable authority where available.
- Do not claim a Lean proof until it compiles with the declared Lean/mathlib
  version. The current environment may lack Lean; record that fact explicitly.
- The project uses Lean core only. Do not download mathlib or use post-Newtonian
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
- Current handoff: research/HANDOFF-2026-10-06-REWORKED-SOURCES.md.
  The user retired the 4 October handoff as an execution plan after the
  source refactor and bookkeeping cleanup. Preserve its results, but follow
  the new source-local proof order and carried-forward obligations.
