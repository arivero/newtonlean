# Elementary, classical and modern support

Current ownership after the 6 October historical-file refactor is determined
by the actual Lean files/imports. The earlier extraction design is in Git;
its placement of Cauchy machinery in BarrowLib is superseded.

BarrowLib contains rational arithmetic, ordered ratios, finite sums/products,
coordinate point/determinant geometry, finite refinement and explicit
exhaustion arguments. An explicit abstract order/limiting premise must not
hide its desired conclusion. Coordinate L1 bounds are a chosen estimate,
not automatically an intrinsic physical magnitude.

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

`Polygon/SectorFan` represents actual filled triangles and their finite union.
A common positive horizontal half-plane and consecutive nonnegative
determinants derive separating radial cuts. Explicit triangle-area and
nonzero radial-cut additivity rules extend the partial rectangle-area
convention; these extra geometric premises are not derived from rectangle
rules alone. The recursively constructed central polygon then has ordinary
union area equal to half its elapsed time times its initial areal product on
that local sector. This finite identification does not identify a curved
sector or permit a winding fan to be treated as a union without multiplicity.

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
