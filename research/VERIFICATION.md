# Verification record — 2026-09-21

- Lean: 4.19.0, declared by lean-toolchain; default target is the library.
- `lake build` and `lake build NewtonLimitDynamics`: passed. The expanded
  library actually compiled; this is not the previous empty-default-build error.
- `catalogue_formal.py`: 68 theorem declarations inventoried, including private
  helpers, with actual signatures, source correspondence and premise boundaries.
- `check_graph.py`: 57 nodes, 43 classified edges, 176 passage records; source
  identity, TEI anchor/extract agreement and proof/proposed DAG acyclicity passed.
- `lake env lean research/CheckReferences.lean`: 65 public/reference declarations
  elaborated, with axiom inspection. Only standard Lean logical axioms
  `propext`, `Classical.choice`, `Quot.sound` occur; no project axiom or sorryAx.
- `test_evidence_validation.py`: valid baseline passed; stale edge URL,
  cross-stage proof edge, proof cycle and missing anchor were rejected.
- `compare_editions.py`: seven explicit passage alignments generated the report.
  Recorded incoming-edge changes are scoped to those proof passages.
- `sha256sum -c docs/SHA256SUMS`: all twelve source artifacts passed.
- `git diff --check`: passed. The manifest's external package list stays empty.

PDF verification was selective: Royal Society reprint p.36 (H4), Gregory p.336
(booklet proposal), p.339 (C44 identity). TEI checking is transcription checking,
not manuscript-image verification. C42 and exact Newton draft folios remain gaps.

These checks certify the stated Lean implications and data consistency. They do
not turn contact limits, mechanical area identification, curve existence or
secondary-supported manuscript mappings into discharged historical proofs.
