# Verification record — 2026-09-22

- Lean: 4.19.0, declared by lean-toolchain; default target is the library.
- `lake build` and `lake build NewtonLimitDynamics`: passed. The expanded
  library actually compiled; this is not the previous empty-default-build error.
- `catalogue_formal.py`: 97 theorem declarations inventoried, including private
  helpers, with actual signatures, source correspondence and premise boundaries.
- `check_graph.py`: 77 nodes, 68 classified edges, 234 passage records; source
  identity, TEI anchor/extract agreement and proof/proposed DAG acyclicity passed.
- `lake env lean research/CheckReferences.lean`: 94 public/reference declarations
  elaborated, with axiom inspection. Only standard Lean logical axioms
  `propext`, `Classical.choice`, `Quot.sound` occur; no project axiom or sorryAx.
- `test_evidence_validation.py`: valid baseline passed; stale edge URL,
  cross-stage proof edge, proof cycle and missing anchor were rejected.
- `compare_editions.py`: seven explicit passage alignments generated the report.
  Recorded incoming-edge changes are scoped to those proof passages.
- `collate_sources.py`: nine witnesses and 231 selected XML anchors collated;
  all generated extracts matched the TEI anchors, 51 anchors retained revision
  markup, and page/facsimile metadata was recorded. Local HTML anchor presence
  is reported separately (226 normalized and 231 diplomatic matches); three PDF
  or secondary records remain supplementary and unanchored. No image was
  downloaded or read.
- `sha256sum -c docs/SHA256SUMS`: all twenty-two listed source artifacts passed.
- `git diff --check`: passed. The manifest's external package list stays empty.

PDF verification was selective: Royal Society reprint p.36 (H4), Gregory p.336
(booklet proposal), p.339 (C44 identity). TEI checking is transcription checking,
not manuscript-image verification. C42 and exact Newton draft folios remain gaps.

These checks certify the stated Lean implications and data consistency. They do
not turn contact limits, mechanical area identification, curve existence or
secondary-supported manuscript mappings into discharged historical proofs.

Finite refinement-strip follow-up: Terra reran both builds, the formal
catalogue, graph/reference generation, Lean reference/axiom inspection and
whitespace check successfully. The new results use finite determinant and
triangle arithmetic only, with no integral calculus or limiting theorem.
They establish a spatially compatible one-cell strip, not a common-force time
refinement or an existing limiting curve. Source collation, archive hashes and
evidence regression results above are retained from the preceding validation;
unchanged sources were not revalidated for this code-only follow-up.

Time-subdivision follow-up: `lake build`, `lake build NewtonLimitDynamics`,
`catalogue_formal.py` (114 theorem declarations), `check_graph.py` (77 nodes,
68 edges, 234 passages, 106 Lean references), `CheckReferences.lean` (106
declarations inspected), and `git diff --check` passed. The new finite rational
diagnostic has no `sorryAx` or project axioms; only standard logical axioms
(`propext`, `Classical.choice`, `Quot.sound`) occur in dependency reports.
Its endpoint mismatch, equal terminal velocity, connector, and signed boundary
example are finite constructions only; no limiting curve, integral calculus,
or trajectory-existence claim is discharged.

Partition-control follow-up: `lake build` and `lake build NewtonLimitDynamics`
passed, and the regenerated catalogue contains 139 theorem declarations.
`check_graph.py` passed with 77 nodes, 68 classified edges, 234 passage
records, and 118 Lean references. `CheckReferences.lean` elaborated all 118
checked declarations; its axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or project axiom. The
new public results are finite: `partitionMotion_formula` explicitly unfolds
the repeated `TimeSubdivision.endKick` recurrence,
`candidate_partitionMotion_residual` gives the exact rational-time residual
`(Q/(2D²))*a`, and `residual_mesh_bound` gives its nonnegative maximum-cell
coefficient bound. No convergence, limiting curve, integral calculus, or
trajectory-existence claim is discharged. `git diff --check` passed; generated
`research/formal-results.json` was regenerated and conversation-export changes
remain preserved.
