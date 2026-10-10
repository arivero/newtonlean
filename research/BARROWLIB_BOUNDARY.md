# Elementary, classical and modern support

The user clarified chronological ownership on 7 October: ClassicsLib covers
classical results through Hypatia; BarrowLib covers results after Hypatia and
before the Principia; ModernLib covers any result after the Principia.
The user's explicit exception places pre-Principia Chinese results in
ClassicsLib. Arabic results belong in BarrowLib when dated after Hypatia and
before the Principia. These are repository ownership conventions, not claims
of a single chronological or geographical development of mathematics.
The date of a Lean encoding does not change the date of its mathematical
content. Newton's own results stay in their historical witness files.
These scopes are comments at the start of all three library entry points.
Every borrowed library result needs an exact original-language passage with
its author, work, location and URL. Unicode comments retain Greek and Latin.
A background citation does not source an exact derived helper. AI-derived
project results may identify their own statement/proof as their source, but
known results retain their attribution; formalization is not discovery.
For such derived results, Classics-only dependencies give Classics support,
Barrow plus Classics gives Barrow support, and modern use gives Modern support.
The existing libraries' exact-result source audit remains open; their names
alone do not certify that each attribution has been established.
The earlier extraction design is in Git; its placement of Cauchy machinery
in BarrowLib is superseded. Existing arithmetic/data infrastructure is used
to encode the mathematics, not as evidence for its historical availability.

User decision, 10 October: Lean 4.34.1 core types and lemmas, including
`Rat`, are encoding infrastructure outside project M/H scores. Rational
arithmetic belongs to core Rat. FiniteRecurrence now uses Rat directly;
its finite bounds and the shared FinitePowers induction are project
derivations with their exact statements/proofs as provenance, rather than
historical attestations. Temporary legacy adapters normalize numerical
bounds only, preserving their values without changing actual state inputs.
Rational.magnitudes in Common/RatMagnitudes
now realizes the ordered interface over Rat independently of legacy Fraction,
and rational closed-bound exhaustion uses its half-gap
witness directly over Rat. The legacy unreduced Fraction and its other clients
remain temporarily during the staged conversion. Moving those existing
helpers alone would change provenance, not their count or completion.

Classical attestation is now recorded separately in
[ClassicsLib/NineChapters/FractionRules.lean](../ClassicsLib/NineChapters/FractionRules.lean),
with [chapter-I](../docs/classics/nine-chapters-I.md) and
[chapter-VIII](../docs/classics/nine-chapters-VIII.md) Chinese witnesses.
Positive fraction reduction, addition, smaller-from-larger subtraction,
product and division are source matches. Identifying the subtractive common
measure with Nat.gcd, extracting a comparison iff, averaging with a list,
and representing signed-whole addition/subtraction by Rat require stated
qualifications. Liu Hui's 263 commentary on naming 正/負 is separate from 術.
These ten theorems are attestation only; no existing proof depends on them.
Core convenience does not establish historical availability.

The Nine Chapters passages here do not attest signed multiplication,
general arithmetic with zero or signed order. The explicit 無入 cases encode
absent entries only. A surviving non-core claim needing those sources must
receive its own exact original-language passage; the audit remains open in
[STATE.md](STATE.md). Euclid VII.19 would concern positive cross-products,
not these additional operations. The abstract Magnitudes/MagnitudeContent
ratio and halving rules remain a separate interface with their own sources.

BarrowLib retains ordered magnitudes, finite sums/products, coordinate
point/determinant geometry, finite refinement and explicit exhaustion
arguments while arithmetic clients migrate. An abstract order or limiting
premise must not hide its desired conclusion. Coordinate L1 bounds are a
chosen estimate, not automatically an intrinsic physical magnitude.

`Common/Exhaustion` supplies an ordered positive-difference contradiction,
including a nonempty before-end time window; it constructs no terminal value.
`Polygon/RectangleContent` derives finite union areas from explicit rectangle,
separated-additivity and monotonicity rules. Its partial `HasArea` relation does
not assert rational area for arbitrary figures; a given curved area is a
separate premise. Unit ratios require a positive fixed area.
`Polygon/RationalBoundary` proves finite rational endpoint-cover, chord and
supporting-segment estimates and their two-sided exhaustion under supplied
uniform continuity. It constructs no completion, derivative, tangent or
arclength. These declarations cannot discharge the mechanical correspondence
between a given trajectory and Newton's polygons.

`BarrowLib/Polygon/SectorFan` represents filled triangles and their finite union.
A common positive horizontal half-plane and consecutive nonnegative
determinants derive separating radial cuts. Explicit triangle-area and
nonzero radial-cut additivity rules extend the partial rectangle-area
convention; these extra geometric premises are not derived from rectangle
rules alone. Euclid I.41 and Common Notions 2–5 identify the classical area
principles; the coordinate dissection is a reconstruction, not a full
synthetic proof of those supplied rules. The exact coordinate lemmas are
project derivations using Barrow support, so they belong in BarrowLib under
the user's dependency rule, rather than acquiring classical status from the
background quotations. Newton's law-driven application
belongs in Historical/AreaLaw.lean. This finite identification does not
identify a curved sector or permit a winding fan to be treated as a union
without multiplicity.

ClassicsLib identifies the classical source result, currently Euclid I.37
and I.38 coordinate special cases and their finite lattice realization.
A determinant implementation is not a completed synthetic Euclidean proof.
Classical support may use BarrowLib.

ModernLib contains Cauchy names and quotient values, completed time/position/
scalar operations, metric closure, Lipschitz-oracle reconstruction and the
modern supplied-curve consistency route. Shared BinaryLift and completed
pairings/secants avoid repeating completion proofs. General force and harmonic
clients retain their distinct coefficients and explicit calibrated/regional
premises. Coordinate Euclidean dot products and L1 error gauges stay distinct.

Historical files own one result with separate edition/witness sections.
Primary proofs may use elementary/classical support and untainted historical
results. Modern proofs remain below the five-line anachronical separator;
their types and dependencies taint downstream use. Supporting libraries do
not import historical files. Generic mathematics is not historical merely
because it uses a Newton-themed namespace.

Actual polygon fans count multiplicity. Square-cover content and signed
completed tangent triangles are separate geometric objects; neither asserts
ordinary sector-union area or a mechanical potential identity. Conditional
contact arithmetic is not a proved curve/tangent construction.

Build all four library targets and run CheckReferences.lean to check the
compiled proof boundary. The source-specific correspondence and outstanding
mechanical/geometric premises remain in the historical files and STATE.md.
Relocation, interfaces and these boundary notes add no historical proof credit.

Anachronical proofs carry a `Modern dependency score: M/(M+H)` comment at their
start. The compiled checker counts distinct source-declared project theorems
and axioms transitively through bodies, types, definitions and private helpers;
it excludes the root proof, generated auxiliaries and standard Lean support.
Both raw counts are retained. Prefer a smaller modern fraction and burden;
adding irrelevant historical helpers is not improvement. A dependency-free
proof displays 0, with both raw counts zero. Modern definitions
still taint historical use even when no modern theorem is counted. This score
reflects current dependency classification, not source-audit completion or a
mathematical proof that the minimum among all possible proofs was attained.
