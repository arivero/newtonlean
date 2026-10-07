# Newton's changing proof architecture

This repository formalizes Newton's Book I, Section II, Propositions I–IV in
Lean 4.19.0 core/Std, with no mathlib. De Motu antecedents, the 1687 edition
and the 1713 edition keep their own statements, proof passages and premises.
Proposed 1694 and 1726 material serves comparison without supplying earlier
premises silently.

Start with [the goals](research/GOALS.md),
[the current handoff](research/HANDOFF-2026-10-06-REWORKED-SOURCES.md) and
[state and open obligations](research/STATE.md). Proposition I comes first.
The complete historical proofs remain open; finite, conditional and modern
results are labelled by their actual scope. Theorem counts and estimated
percentages are not completion measures.

## Historical files and libraries

[Historical results](NewtonLimitDynamics/Historical/) have one file per theorem,
lemma, law or corollary, with separate witness sections. Each section contains
exact Latin, source path/hash/URL, proof correspondence, definitions and checked
results. Newton Project TEI in docs/m1 and docs/m4 is the transcription authority;
see [source coverage](research/sources.md).

BarrowLib contains elementary arithmetic, finite geometry and explicit
exhaustion arguments. ClassicsLib contains source-identified classical
mathematics, currently Euclidean coordinate special cases. ModernLib contains
completion, modern motion constructions and diagnostics. Primary historical
proofs use elementary/classical support and untainted historical results.
Anachronical proofs occupy a section below five full lines of `=` and
`ANACHRONICAL PROOFS`. Modern use taints downstream types and proofs, including
private helpers and uses across files. An import alone does not classify every
declaration in a file.

The trajectory is given explicitly in the primary route, with mechanical laws
and regularity separately stated. Proposition I must prove swept sector areas
proportional to time. Nonnegative area between the curve and Newton's polygon
is separate approximation control. Neither area conclusion nor polygon/curve
agreement is included in existence.

The retained general construction proves local interval fan proportionality
and between-path content decay under regional calibrated conditions. A given-
trajectory theorem derives the same conclusions under explicit local consistency.
Ordinary swept-sector identification and the historical limiting proof remain
open. The next increment is Lemma I, then the invoked Lemmas II–III and corollary
chain. Kepler is a later application of the general Proposition I proof.

The [Latin proof route](research/PROP_I_REALIZATION.md),
[two-area distinction](research/PROP_I_PATH_DEFECT.md),
[construction](research/CAUCHY_REALIZATION.md) and
[dependency diagrams](research/figures.md) give focused details. Diagrams derive
from current historical source comments and compiled declarations. The separate
[action arguments](research/action-arguments/README.md) supply no historical
premises or assumed universal constant.

## Reverse programme

[Reverse/](Reverse/README.md) runs the opposite direction: a quantum
Kaluza–Klein parent is reduced through named interfaces (KK reduction, weak
decoupling, colour scale, mass gap, confinement, neutral matter,
nonrelativistic and semiclassical limits) to the same Law I / Law II shapes
the historical files consume. It is modern, imports nothing historical and
is imported by nothing historical; `lake build Reverse` builds it.

## Verification

```sh
lake build
lake build Reverse
lake build BarrowLib
lake build ClassicsLib
lake build ModernLib
lake build NewtonLimitDynamics
lake env lean research/CheckReferences.lean
lake env lean scripts/inspect_graphs.lean
sha256sum -c docs/SHA256SUMS
git diff HEAD --check
```

Run the retained Lean scope harnesses described in [verification](research/VERIFICATION.md).
Passing checks certify the stated Lean results without discharging supplied
historical premises. Git retains previous tools, figures and session records;
there are no JSON catalogs, Python bookkeeping scripts or completion plots.

Readable source-specific notes remain in Markdown. Render them on demand:

```sh
pandoc docs/reference/principia-1687-modern.md -o /tmp/principia-1687-modern.pdf \
  --pdf-engine=xelatex -V mainfont='DejaVu Serif' \
  -V monofont='DejaVu Sans Mono' -V mathfont='DejaVu Math TeX Gyre' \
  --toc --toc-depth=2
```

The reader renderings are aids; original sources and historical Lean witness
sections remain authoritative. The [theorem-growth analysis](research/THEOREM_PROLIFERATION.md)
explains why infrastructure and interface counts do not measure discharged
proof obligations.

## Related work and historical proof ordering

Several formalization projects attend to historical sources, proof order and
provenance. [LeanEuclid][leaneuclid] (Murphy et al., ICML 2024) implements in
Lean a variant of System E, which Avigad, Dean and Mumma designed as a faithful
model of the proofs in Euclid's *Elements*, diagrammatic reasoning included.
Its Book I proofs are written to follow Euclid's own arguments closely, with
SMT solvers carrying out the diagrammatic inferences implicitly. Its target is
Euclid's proof practice as well as his theorems.

The closest methodological precedent is
[*Does the Proof Prove It That Way?*][pistis] (Mao et al., 2026). Its Pistis
system formalizes Books I–III of the *Elements* under five necessary
conditions of faithfulness. Formal steps correspond to the source sentences in
their order, and every proposition Euclid cites in a step must already be
available there and applied at that step. A compiling proof of the same theorem
by another route fails these conditions. The method therefore constrains which
earlier propositions and proof steps a formal proof may use.

[Lean of the Mathematical Commons][lmc] is a source-linked Lean 4 library for
classical mathematics, piloted on Emmy Noether's works. It links its entries to
historical source editions, audits Mathlib coverage declaration by declaration
and records formalization gaps. The Mathlib Initiative's
[Formal Frontier][formal-frontier] programme is preparing an autoformalization
specification that will set community standards for how formal code relates
to its informal source and what counts as adequate coverage and faithfulness.
Both concern provenance and source linking; Mathlib itself is organized by
mathematical subject.

newtonlean applies a related idea to Newton's changing proof architecture.
Declarations are separated by historical witness and edition, and a result in
an earlier layer may be repaired only with mathematics and textual assumptions
admitted to that layer. Conceptually, the project treats mathematical knowledge
as a dated filtration

$$\mathcal M_{t_1} \subseteq \mathcal M_{t_2} \subseteq \cdots,$$

in which a historical proof at date or edition $t$ depends only on results and
assumptions admitted into $\mathcal M_t$. A modern dependency DAG records what a
proof uses; the filtration also records whether each use was admissible at $t$.
The library conventions give a coarse version of these layers: ClassicsLib
through Hypatia, BarrowLib after Hypatia and before the Principia, ModernLib
after the Principia. Modern reconstructions remain useful and stay in the marked
anachronical sections, with their taint traced through compiled dependencies.

For Newton the ordering is edition-sensitive as well as chronological, because
he revised the text whose proofs are being formalized. *De Motu*, the 1687
edition, the 1713 edition and later witnesses can differ in statement, premises
and proof architecture. A later edition is therefore evidence for comparison,
not automatically a premise of an earlier proof. The novelty claimed here is
correspondingly narrow: source- and edition-sensitive formalization of
Newton's proof architecture; explicit separation of historical and anachronical
proof resources; treatment of the dependency graph itself as an object of
historical investigation; and, as the work proceeds, a visible record of where
physical assumptions such as Galilean kinematics, or particular limiting
choices, enter a proof.

### References

- Jeremy Avigad, Edward Dean and John Mumma, “A formal system for Euclid's
  *Elements*”, *Review of Symbolic Logic* 2(4), 2009, 700–768,
  [doi:10.1017/S1755020309990098](https://doi.org/10.1017/S1755020309990098),
  [arXiv:0810.4315](https://arxiv.org/abs/0810.4315).
- Logan Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar and
  Xujie Si, “Autoformalizing Euclidean Geometry”, ICML 2024,
  [arXiv:2405.17216](https://arxiv.org/abs/2405.17216); code:
  [LeanEuclid][leaneuclid].
- Tadd Mao, Tianjun Zhong, Dhruva Arekar, Yuming Feng, One An, Jiani Huang,
  Xujie Si and Ziyang Li, “Does the Proof Prove It That Way? Faithful
  Formalization of Elements Proofs”, 2026, [arXiv:2608.15432][pistis].
- [Lean of the Mathematical Commons][lmc], Emmy Noether pilot, concept DOI
  [10.5281/zenodo.21129945](https://doi.org/10.5281/zenodo.21129945).
- Mathlib Initiative, [Formal Frontier][formal-frontier].

[leaneuclid]: https://github.com/loganrjmurphy/LeanEuclid
[pistis]: https://arxiv.org/abs/2608.15432
[lmc]: https://github.com/KokunoYumeto/lean-mathematical-commons
[formal-frontier]: https://mathlib-initiative.org/formal-frontier/
