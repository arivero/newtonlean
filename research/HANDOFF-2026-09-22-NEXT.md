# Handoff to the next agent (22 September 2026, end of the Claude Code session)

Written by Claude Code (Claude Opus 5.5) at the close of its session. It
supersedes [HANDOFF-CLAUDE-CODE.md](HANDOFF-CLAUDE-CODE.md), whose bounded
task (`Polygon/PartialCell.lean`) is done.

## Read order

1. `AGENTS.md` (project rules and model policy), then this file.
2. `research/STATE.md`, `research/TASKS.md`, `research/GOALS.md`.
3. For order 4: `research/PROP_I_REALIZATION.md`. For the action layer:
   `research/action-arguments/README.md`.
4. Only then the Lean modules relevant to the chosen task.

Recover the live state first: `git log --oneline -25`, `git status -sb`.

## Standing constraints (details in AGENTS.md and GOALS.md)

- Keep De Motu, 1687 and 1713 separate; proposed 1694 and 1726 are
  comparisons. M1–M4 remain supporting work and are **not** certified complete.
- Lean 4.19.0, core/Std only: no mathlib, no downloads, no `sorry`, no project
  axioms. Run both `lake build` and `lake build NewtonLimitDynamics`.
- Execution is sequential, at most one subagent at a time. For Codex, the
  AGENTS.md v6 model policy applies. The user told Claude Code that it may
  delegate menial work (check runs, bookkeeping) to smaller models.
- Preserve the unrelated conversation-export changes: the deletion of
  `conversation-continue-planck-gap-analysis.md` and the untracked
  `continue-planck-gap-analysis.md`. Neither stage nor restore them.
- The action (Planck) hypothesis lives in a separate diagnostic layer and never
  closes a historical proof.

## User directions from this session

- **Action arguments:** develop arguments *for* a nonzero constant, grounded in
  the Latin and in the differences between Newton's versions. Arguments
  against are not to be extended (Arg001 stays as recorded).
- **File naming** in `research/action-arguments/`:
  `YYMMDD<model>v<version>Arg<NNN>.md`, with the argument number shared across
  models. Each file states its verdict, sources, step statuses and GOALS.md
  tests.

## Verified state at handoff

Both builds pass; 284 catalogued theorem declarations; `check_graph.py`
validates 77 nodes, 68 edges and 246 passages and emits 220 references;
`CheckReferences.lean` elaborates all of them with only `propext`,
`Classical.choice` and `Quot.sound`. The passage store has 243 collated TEI
anchors. All README verification scripts pass. Counts and scopes for each step
are in `research/VERIFICATION.md`.

## What this session added (commits after `71d8cf6`)

| Commit | Result |
| --- | --- |
| `8277e17` | Codex's pending `InertialDefect.lean` and the Claude handoff, finalized |
| `6786fbc` | `PartialCell.lean`: exact within-cell residual and mesh bound |
| `439ea23` | `UniformRefinement.lean`: explicit refinement below any rational tolerance |
| `0b74518`, `3a9e6c7`, `b7a6d26`, `087eddd` | `PartitionComparison.lean`: exact comparison of arbitrary partitions (positions, partial cells, velocities, `partition_gap`) |
| `087eddd`, `6f3379f` | `Converse.lean`: finite Proposition II step, Case 1 and Case 2, with counterexamples |
| `7a41f91` | `CentralSchedule.lean` and `PROP_I_REALIZATION.md`: area law for any central field with unequal cells; exact refinement identities; unequal-cell converse |
| `f687af6`, `38bf336` | `HarmonicStability.lean`: exact equal-cell invariant and mesh-uniform bounds |
| `f6e16d0`, `e300334`, `0df8b16`, `bd3abba` | `action-arguments/` Arg001–Arg006; `Diagnostic/InverseCubeAreal.lean`, `Diagnostic/PhaseArea.lean`, `Polygon/MonotoneEnclosure.lean` |
| `b22537b`, `5b2bbfa` | Twelve TEI anchors added (Section I Scholium, Prop. IX, XLI Cor. 3, XLV Cor. 1) |

## Programme status (TASKS.md orders)

| Order | Status | Open |
| --- | --- | --- |
| 1 source map | done | — |
| 2 contact and restart | done | — |
| 3 time subdivision | constant force at rational times closed (`partition_gap`) | absolute strip-area sums; times beyond the rationals; varying force |
| 4 Prop. I realization | P1 checked in general, P2 exact identities, P3 stability for the harmonic field | P3 convergence; P4 conditional on P3; P5 force identification |
| 5 Prop. II converse | finite Case 1, Case 2, unequal cells | vanishing-triangle passage from a given curve; the inward sense premise |
| 6 Prop. III | **not started**; Latin read | see task 1 below |
| 7 Prop. IV | not started (only the diagnostic `InverseCubeAreal`) | circular comparison along each edition's route |
| 8 action diagnostic | Arg001–Arg006 | "for" next checks below |

## Next bounded tasks, in order

1. **Proposition III finite step (order 6).** Sources: 1687 NATP00077
   par53–54, 1713 NATP00082 par64–65. Both proofs run through the laws'
   Corollary VI, then Law I, then Proposition II. Plan, on `LatticePoint` like
   `Converse.lean`:
   - build vertex sequences from two initial vertices and a deflection history
     (pair recursion);
   - Corollary VI finite: a common added deflection leaves the relative
     sequence unchanged;
   - Law I finite: zero deflection gives `centreAt` uniform motion;
   - conclude with `Converse.moving_centre_equal_areas_central`: equal
     relative areas imply that the difference of deflections is parallel to
     the relative radius.

   Newton's route is primary; the direct relative-coordinate route serves as
   a check.
2. **Action layer, "for" next checks.**
   - Arg004: a Cavalieri strip decomposition giving polygon-area preservation
     for nonlinear fields; the planar symplectic check for central fields.
   - Arg006: the discrete curvature radius of the constructed polygon against
     `p²/(m|F_⊥|)` for constant and harmonic fields.
   - Arg005: a rational-cell `MonotoneEnclosure`; identify `tri` with the
     `PartitionControl` cross statistic.
3. **Order 4, P3 convergence** for the harmonic field at rational times. The
   cell map is linear, so the difference of two trajectories is a trajectory
   and the invariant quadratic form bounds it exactly. The local defect
   between one cell and two half cells is second order in the cell. What is
   still needed is a Cauchy–Schwarz or triangle inequality for the form in
   `Fraction` arithmetic.
4. **Order 7**, Proposition IV: the 1687 route (Prop. II, Lemma V, Lemma XI)
   and the 1713 route (Prop. II, Prop. I Cor. 2 and 4, Lemma VII), kept
   separate.
5. **Order 3 remainder.** For constant force, each two-cell chord triangle of
   the constructed polygon has doubled area `h³·det(v, a)`, the same for every
   pair since `det(v + s·a, a) = det(v, a)`. So the absolute sum equals the
   signed one, `N·h³·det(v, a) = (T/2)·h²·det(v, a)`. This was computed by
   hand and has not been formalized.

## Working notes

- Fraction identities: `unfold …; dsimp; simp only [Int.add_mul, Int.mul_add,
  Int.neg_mul, Int.mul_neg]; ac_nf; omega` proves most of them. Avoid numeric
  literals inside fractions (write `c + c`); `decide` evaluates concrete
  fractions. When `simp` turns a conjunct into `True`, use
  `refine ⟨trivial, ?_⟩`.
- Every `.lean` file under `NewtonLimitDynamics/` needs a
  `scripts/catalogue_formal.py` entry whose passage ids exist in
  `research/passages.json`, or `check_graph.py` fails.
- Adding passages: extend `research/selections.json` and
  `research/passage-annotations.json`, then run `catalogue_m1.py`,
  `collate_sources.py`, `compare_editions.py`, `check_graph.py` and
  `test_evidence_validation.py`, and update the anchor counts in M4.md.
- The machine clock lagged real elapsed time during this session; do not rely
  on it for timed work windows.
