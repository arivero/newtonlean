# Historical result files

One file per result; witnesses have separate Latin and formalization sections.
Text-only sections record open obligations, not unproved Lean axioms.

Primary and anachronical counts include definitions and partial results; they are not counts of completed Newton proofs.

| Result | Lean file | Witnesses | Primary declarations | Anachronical declarations |
| --- | --- | --- | --- | --- |
| area_law | [AreaLaw](../NewtonLimitDynamics/Historical/AreaLaw.lean) | NATP00089, NATP00090, 1687, 1713 | 8 | 14 |
| composition_of_motions | [CompositionOfMotions](../NewtonLimitDynamics/Historical/CompositionOfMotions.lean) | NATP00089, NATP00090, 1687, 1713 | 6 | 0 |
| lemma_i | [LemmaI](../NewtonLimitDynamics/Historical/LemmaI.lean) | 1687, 1713 | 0 | 0 |
| lemma_ii | [LemmaII](../NewtonLimitDynamics/Historical/LemmaII.lean) | 1687, 1713 | 2 | 0 |
| lemma_iii | [LemmaIII](../NewtonLimitDynamics/Historical/LemmaIII.lean) | 1687, 1713 | 0 | 0 |
| lemma_iii_corollary_i | [CorollaryI](../NewtonLimitDynamics/Historical/LemmaIII/CorollaryI.lean) | 1687, 1713 | 0 | 0 |
| lemma_iii_corollary_ii | [CorollaryII](../NewtonLimitDynamics/Historical/LemmaIII/CorollaryII.lean) | 1687, 1713 | 0 | 0 |
| lemma_iii_corollary_iii | [CorollaryIII](../NewtonLimitDynamics/Historical/LemmaIII/CorollaryIII.lean) | 1687, 1713 | 0 | 0 |
| lemma_iii_corollary_iv | [CorollaryIV](../NewtonLimitDynamics/Historical/LemmaIII/CorollaryIV.lean) | 1687, 1713 | 0 | 4 |
| lemma_x | [LemmaX](../NewtonLimitDynamics/Historical/LemmaX.lean) | 1687, 1713 | 7 | 0 |
| lemma_x_corollary_iv | [CorollaryIV](../NewtonLimitDynamics/Historical/LemmaX/CorollaryIV.lean) | 1713 | 1 | 0 |
| lemma_x_corollary_v | [CorollaryV](../NewtonLimitDynamics/Historical/LemmaX/CorollaryV.lean) | 1713 | 1 | 0 |
| law_i | [LawI](../NewtonLimitDynamics/Historical/LawI.lean) | 1687, 1713 | 0 | 0 |
| law_ii | [LawII](../NewtonLimitDynamics/Historical/LawII.lean) | 1687, 1713 | 0 | 0 |
| proposition_ii | [PropositionII](../NewtonLimitDynamics/Historical/PropositionII.lean) | 1687, 1713 | 0 | 0 |
| proposition_iii | [PropositionIII](../NewtonLimitDynamics/Historical/PropositionIII.lean) | 1687, 1713 | 0 | 0 |
| proposition_iv | [PropositionIV](../NewtonLimitDynamics/Historical/PropositionIV.lean) | 1687, 1713 | 0 | 0 |
| laws_corollary_v | [LawsCorollaryV](../NewtonLimitDynamics/Historical/LawsCorollaryV.lean) | 1687, 1713 | 0 | 0 |
| laws_corollary_vi | [LawsCorollaryVI](../NewtonLimitDynamics/Historical/LawsCorollaryVI.lean) | 1687, 1713 | 0 | 0 |

Source hashes, exact paragraph anchors, URLs, textual-layer rules and status are in [historical-units.json](historical-units.json). Source identity and library boundaries are checked by `python3 scripts/check_architecture.py`. Completion scores are unchanged by relocation.

[proof-dependencies.json](proof-dependencies.json) records compiled uses, transitive anachronical taint and missing formal uses of source-evidenced dependencies. Regenerate it with `python3 scripts/check_proof_layers.py --report research/proof-dependencies.json`.
