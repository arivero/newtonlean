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

Each file states its verdict (`supports` with its scope — the kind, the
location, or the scale of a constant — `against`, or `inconclusive`), the sources and checked Lean results it uses, the status of
every step (`explicit_dependency`, `implicit_dependency`,
`modern_reconstruction`, `editorial_interpretation`), and which GOALS.md tests
it passes: positivity, finiteness, partition stability, system independence,
and action-rescaling freedom.

## Index

| File | Proposer | Verdict | Summary |
| --- | --- | --- | --- |
| [260922opus5.5v1Arg001.md](260922opus5.5v1Arg001.md) | Claude Opus 5.5 | against (for the routes checked) | Every checked finite refinement residual vanishes linearly with the mesh; the constructions select no action floor |
| [260922opus5.5v1Arg002.md](260922opus5.5v1Arg002.md) | Claude Opus 5.5 | inconclusive; fails system independence | Proposition IV Cor. 1 (with 1713 Cor. 7): inverse-cube circles are the one power law with a common areal velocity, `√(m*k)`, which also bounds the Prop. IX spirals; the action is system-fixed |
| [260922opus5.5v1Arg003.md](260922opus5.5v1Arg003.md) | Claude Opus 5.5 | inconclusive; locates, derives none | Prop. XLI Cor. 3 and XLV Cor. 1: the inverse cube bounds centre-avoiding motion, where the finite-force premise holds; for that law the boundary is the action `√(m*k)`, for gravity it is zero |
| [260922opus5.5v1Arg004.md](260922opus5.5v1Arg004.md) | Claude Opus 5.5 | supports the kind; value undetermined | De Motu *momenta* → 1687/1713 *particulæ* and ultimate ratios; new 1713 Prop. I Cor. 1 (velocity × perpendicular). The construction's exact invariants that survive every mesh and every force (phase area, areal product) are actions |
| [260922opus5.5v1Arg005.md](260922opus5.5v1Arg005.md) | Claude Opus 5.5 | supports the location | Hyp. 4 → Lemma 2 → Lemma X *vi regulari* → 1713 *Vi finita … continuo augetur vel continuo diminuatur* with new Cor. 3–5; finite enclosure holds under the clause and fails without it; a nonzero action limits the law to `t ≳ (mħ/F²)^{1/3}` |
| [260922opus5.5v1Arg006.md](260922opus5.5v1Arg006.md) | Claude Opus 5.5 | supports that the scale is an action | 1713 *Vi finita* (Lemma X) and *curvaturam finitam* (Lemma XI) bound one local action `p·ρ_F`; Newton compares with circles, without a unit; the quasi-classical condition is `p·ρ_F ≫ ħ` |

Direction (user, 22 September 2026): develop arguments *for* a nonzero
constant, grounded in the Latin and in the differences between Newton's
versions. Arguments against are not being extended; Arg001 stays as recorded.

Status on 22 September 2026: the arguments for identify action as the one
kind of universal minimum Newton's revised method admits (Arg004), the premise
through which it would act (Arg005), and the local quantity it would bound
(Arg006). None fixes a value. Identifying the value with Planck's constant
needs a physical bridge from outside the *Principia*.
