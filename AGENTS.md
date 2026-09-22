# Project method

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
