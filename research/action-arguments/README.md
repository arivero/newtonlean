# Action-constant arguments

This folder collects candidate arguments for, or against, a nonzero universal
action constant drawn from analysis of the *Principia* and its antecedents.
It belongs to the separate diagnostic layer of GOALS.md ("Action hypothesis
and its possible rejection"). No file here supplies a premise to a historical
proof, and no argument is promoted to a result without a checked theorem.

## File naming

`YYMMDD<model>v<version>Arg<NNN>.md`

- `YYMMDD`: date written (e.g. `260922` = 22 September 2026).
- `<model>`: the model that proposes the argument (e.g. `opus5.5` for Claude
  Opus 5.5; `gpt6sol` for GPT-6 Sol).
- `v<version>`: revision of that argument by that model.
- `Arg<NNN>`: argument number, shared across models so that critiques and
  revisions of one argument keep its number.

Each file states its verdict (`supports nonzero constant`, `against`,
`inconclusive`), the sources and checked Lean results it uses, the status of
every step (`explicit_dependency`, `implicit_dependency`,
`modern_reconstruction`, `editorial_interpretation`), and which GOALS.md tests
it passes: positivity, finiteness, partition stability, system independence,
and action-rescaling freedom.

## Index

| File | Proposer | Verdict | Summary |
| --- | --- | --- | --- |
| [260922opus5.5v1Arg001.md](260922opus5.5v1Arg001.md) | Claude Opus 5.5 | against (for the routes checked) | Every checked finite refinement residual vanishes linearly with the mesh; the constructions select no action floor |
| [260922opus5.5v1Arg002.md](260922opus5.5v1Arg002.md) | Claude Opus 5.5 | inconclusive; fails system independence | Proposition IV Cor. 1 (with 1713 Cor. 7): inverse-cube circles are the one power law with a common areal velocity, `√(m*k)`, which also bounds the Prop. IX spirals; the action is system-fixed |

Status on 22 September 2026: **no argument here establishes a nonzero
universal action constant.**
