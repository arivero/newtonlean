# One historical result per file

The user selected this architecture on 6 October 2026. The refactor and
source-only cleanup were committed and pushed as `60180f2` after release of
the review hold. Subsequent cleanup removes generated whole-library outputs,
Python, plots and session records; Git preserves the earlier design and checks.

## Historical ownership

Each theorem, lemma, law or corollary has one file under
NewtonLimitDynamics/Historical. Distinct edition/witness sections contain
exact Latin statement and proof, local TEI path/hash, paragraph URLs, proof
correspondence, explicit premises and the checked formalization available.
De Motu's Theorem I is not retrospectively numbered Proposition I. NATP00089
and NATP00090 revisions remain separate; so do 1687, 1713 and comparisons.

Dependencies require the exact passage, witness, URL, status and confidence.
A source that places one result after another does not establish proof use.
Primary proofs use BarrowLib, ClassicsLib and untainted historical results.
Anachronical proofs remain in a separate section of their result file:

```lean
/-
===============================================================================
===============================================================================
===============================================================================
===============================================================================
===============================================================================
ANACHRONICAL PROOFS
-/
```

Modern use taints downstream proof bodies and types, including private helpers
and uses across files. A file import alone does not taint all its declarations.
The direct compiled check verifies this boundary, not completion of Newton's
proof. An unfinished result contains accurate partial scope, never sorry or
a theorem-shaped project axiom.

## Text and library boundaries

Diplomatic rendering retains orig spelling, marked additions/deletions/notes/
unclear readings and documented whitespace normalization. TEI `fw` catchwords
and page furniture are omitted while retaining following text. NATP00090's
`describens42 describens` artifact is removed; the suspicious 1713 `Ipsi S BS`
remains because it is the TEI body reading. Sources and hashes stay unchanged.

BarrowLib owns elementary arithmetic, finite geometry and explicit exhaustion;
ClassicsLib owns source-identified classical mathematics; ModernLib owns Cauchy
completion, metric closure, modern sampled motion and diagnostics. Supporting
libraries do not import historical files. See [the boundary](BARROWLIB_BOUNDARY.md).
Ordinary swept-sector area, multiplicity-counted fans and nonnegative
between-path content remain different objects.

## Deliberate public-name corrections

The refactor preserved prior statements/bodies after nine ownership renames:

| Old name | New name |
| --- | --- |
| DeMotu1684.QuadraticInitialDeflection | NewtonLimitDynamics.QuadraticInitialDeflection |
| Principia1713.quotient | NewtonLimitDynamics.Fraction.quotient |
| Principia1713.generated | NewtonLimitDynamics.Fraction.generated |

The remaining six changes apply separately to 1687 and 1713:
`LemmaIII.lemma2_equal_width_gap` belongs to `LemmaII`;
`LemmaIII.lemmas2_3_monotone_rectangle_reconstruction` belongs to
`ModernLib.Reconstruction.Principia1687.LemmaIIIII` or its 1713 counterpart;
`LemmaIII.corollary3_4_supporting_boundary_reconstruction` belongs to
`ModernLib.Reconstruction.Principia1687.LemmaIIICorollaries` or its 1713 counterpart.
Combined-result support remains modern; new source-local applications do not
turn it into a period proof. Four unused Contact/comparison modules were
subsequently retired, with their declarations preserved in Git.

## Present proof status

Finite equal-area, composition and gap statements are retained. The modern
given-curve, rectangle enclosure and supporting-boundary proofs now have real
applications below the historical files' anachronical separators. The primary
cited historical chain remains to prove; unused imports would not close it.
Read [STATE.md](STATE.md), [the handoff](HANDOFF-2026-10-06-REWORKED-SOURCES.md)
and [verification](VERIFICATION.md). Historical-file relocation and these
applications add no certified Proposition I–IV completion.

Git, current Markdown and Lean files replace the removed JSON inventories and
Python managers. Mermaid figures are views recovered from actual source
comments and compiled declarations, not another authoritative record. Original
TEI/HTML/PDF sources and archive hashes remain; reader Markdown is rendered
only when requested.
