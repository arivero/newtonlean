# Project method

- Work source-first. Preserve Newton's textual stages separately; never merge
  *De Motu*, 1687, proposed 1694, 1713, or 1726 claims silently.
- For every historical edge record the exact passage, witness, URL, status
  (`explicit_dependency`, `implicit_dependency`, `modern_reconstruction`, or
  `editorial_interpretation`), and confidence.
- A source that merely places one result after another does not establish a
  proof dependency. Historical Lean theorems must be named separately from
  modern consequences.
- M1 is the current boundary: quadratic deflection genealogy only. Do not drift
  into quantum mechanics, action scales, or the rest of the *Principia*.
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
