# Quotient polygon map and integer-cell local error, 5 October 2026

This Task B increment is a modern reconstruction. De Motu, 1687 and 1713
claims and source dependencies stay separate. The proof uses Lean core/Std,
rational arithmetic and constructed Cauchy quotients, with no supplied curve.

BinaryCells proves that equivalent addresses at positive T occupy the same
coarse cell or adjacent cells: a gap of two cells leaves time distance at least
H_m, contradicting address equivalence. AffineBoundary uses the actual shared
vertex and the two within-cell intervals to bound both position gaps by the
time-name gap times the sum of the two velocities. Positive scaling tolerances
prove equality of completed positions. Zero T is handled separately.

HarmonicPolygonCurve now constructs polygonMap on the same time quotient as
gammaPosition, proves its whole-edge radius R_m=[2T*M+A_prefix]/2^m and its
uniform convergence. The terminating/nonterminating half-time aliases are in
distinct cells at m=1 and have the same polygon position at every coarse level.
This is address invariance, not arbitrary partition independence.

HarmonicIntegerSubdivision derives exact unequal split position and velocity
defects at actual force samples. A derived finite recurrence bounds k fine
h-cells versus one k*h cell by h²*C(k,w,s). C is finite and independent of h;
nonnegative h, h≤1 and every finite partial duration≤1 are explicit premises.
The local estimate alone does not prove E/G limit agreement for arbitrary k:
propagation over 2^j blocks and its small-window power bound remain unfinished.
The exact earlier three-tick discrepancy still refutes finite schedule equality.

Generic interval, affine-boundary and integer-duration arithmetic belong to
BarrowLib; harmonic coefficients and schedules stay Newton-side. The generic
negation-congruence theorem moves to DyadicArithmetic with its public name and
signature unchanged. No historical edge or external package is added. Explicit
time calibration, general force motion, confinement, restart/gluing, actual
between-path content and P5 remain open; completion scores are unchanged.

The sequential GPT-6 Sol worker supplied the checked local integer-subdivision
estimate, then the service reported model capacity. Root Sol 6.1 implemented
the quotient polygon bridge. Full checks and axioms are recorded in VERIFICATION.md.
