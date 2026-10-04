# General central force design and proof specification

Task A of the 4 October handoff, Sol 6.1. This design is fixed before the
estimates are implemented. Its mathematical layer is `modern_reconstruction`;
it adds no historical edge and imports no limiting theorem into Newton's text.

Use rational vector samples `sample n : Point → Point`, with a named region
`R : Point → Prop` and explicit uniform errors `e_n`. A law is represented by
samples that are Cauchy uniformly on R, not by a rational-valued assertion
that the exact acceleration is rational. Require each finite sample to be
central and inward (a nonnegative rational multiple of the negative radius).
The centre is translated to the origin. The separate parallel-force instance
has no finite centre. The Cauchy quotient later realizes the sampled values;
no limit point is a field of this interface.

This admits irrational magnitudes: for a distance-only law, approximate its
radial scalar coefficient at the squared rational radius. On an annulus
`r₀ ≤ r ≤ R₀`, coefficient error ≤ `e_n/(R₀+1)` gives vector error ≤ `e_n`.
The numerical approximation procedure and its uniform error proof are data of
the law. Neither a square root at a rational point nor an exactly rational
force value is required. The interface also admits continuous
direction-dependent coefficients. Singular laws require an explicit region
and confinement; energy confinement is not assumed proved.

Regularity is a separate contract. For class (a), and for the Lipschitz
subclass of (b), use `|sample n(p)-sample n(q)| ≤ L|p-q|+2e_n`.
Rounding samples need not themselves be Lipschitz. For continuous class (b)
or (c), use an explicit uniform modulus on the confined region with the same
additive sampling error. A modulus of continuity is not a Lipschitz constant.
Class (d) retains finite centrality without a continuity/convergence claim.
Conservative and distance-only qualifications are additional predicates;
they do not participate in the finite perturbation estimate.

Foundation estimates quantify over arbitrary rational point maps and explicit
bounds; Newton-side instances restrict those maps to inward central fields
or the permitted uniform parallel field. The abstract triangular map is

    y = x + h v,    (x,v) ↦ (y, v + h a(y)).

This is finite arithmetic, with no force, derivative or ODE primitive in
BarrowLib. A Newton schedule instantiates this map. Its estimates keep the
position and velocity error terms visible before combining the calibrated
L1 state magnitude. New shared arithmetic and tail lemmas go in BarrowLib;
old public harmonic names remain available as instances or compatibility
facades. The minimal foundation bootstrap precedes use; the rest migrates
in Task D.2.

## First estimate specification

May assume: Fraction order/arithmetic, point triangle/scaling inequalities,
explicit region membership, bounded sampled acceleration B, the displayed
Lipschitz/modulus contract and a bound E comparing two sample maps.
Must not assume: convergence of polygon families, a curve, partition
independence, P5, a potential or a nonzero action constant.

Prove one-map growth, two-map perturbation and coarse/two-half-cell mismatch
for the actual triangular map. Include additive `|h|E` in velocity/state
perturbation and retain the displacement of the sampled arrival point.
Derive finite accumulation from the actual recurrence before claiming a
mesh-uniform or Cauchy result. A supplied adjacent-error field alone is not
a derived estimate for a mechanical family.

Arithmetic pins (Lean exact rationals): harmonic `w=1`, `h=1/8`,
`s=((1,0),(0,1))`; parallel acceleration `(0,-1)` with `h=1/2`; unequal
sample maps `(0,-1)` and `(0,-2)` from the same initial state. Omitting the
`|h|E` term must fail the latter case. Zero L, zero h and zero initial state
must be covered. Unrestricted large-time amplification must not be called
a small-window estimate. Counterexamples may refute an overstrong claim;
compiler rejection alone is never an obstruction.

For merely continuous fields, existence (possibly by a subsequence),
full-sequence convergence and uniqueness are separate obligations. They will
not be replaced by a structure field asserting the desired trajectory.
