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

## Verification

```sh
lake build
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
