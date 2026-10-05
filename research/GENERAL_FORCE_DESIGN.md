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
facades. D.2 now extracts the remaining geometry/completion/time layers and
shares coefficient-parameter tail estimates; force instances stay Newton-side.

## Scales and units

A Lipschitz contract introduces a scale. `L` has units of 1/time² and defines
the local dynamical time `τ_L = 1/√L`: `1/ω` for the harmonic field, about
`√(r³/GM)` for gravity near radius r. The latter shrinks to zero at the
centre, which is why singular laws need a confining region. A mesh converges
once `h ≪ τ_L`. The contract assumes only that a finite `L` exists on the
region; its value depends on the law and the region, rescales with the unit
of time, and fixes no universal constant. A modulus of continuity for classes
(b) and (c) carries the same kind of scale without a single constant.

The retained harmonic and finite refinement estimates use the numerical gauge
τ₀=1. TimeCalibration now carries a positive rational τ₀ explicitly:

    norm_τ(x,v) = |x|+τ₀|v|,
    K_τ(h,L) = (1+|h|/τ₀)(1+τ₀|h|L)
             = 1+|h|(1/τ₀+τ₀L)+h²L.

For n actual cells, the derived dimensionless window
`n|h|(1/τ₀+τ₀L) ≤ 1/2` gives `K_τ^n ≤ 2`. Cross-map sampling discrepancy E
accumulates to at most `2nτ₀|h|E`. The old τ₀=1 product bound and the calibrated
bound share one finite two-factor proof. Fixed positive calibration changes
neither the Cauchy condition nor its completed equivalence class for the
same coordinate family. Under a time-unit change c>0, use

    h→ch, τ₀→cτ₀, v→v/c, L→L/c², E→E/c².

Weighted norms/distances, dimensionless factors/windows and sampling budgets
are proved invariant. Exact harmonic cell mechanics commute with the same
rescaling. Lean controls detect the change in the unweighted state norm if
the calibration is omitted. These are finite estimates and Cauchy-gauge facts;
general motion and restart/gluing remain to be constructed.

τ₀ is a free calibration, not a dynamical necessity or an action constant.
Newton's counterpart is qualitative finiteness (1713 Lemma X *Vi finita*,
Lemma XI *curvaturam finitam*), with no numerical value. Arg006 reads it as a
local scale; no scale created by τ₀ is assigned to the motion itself.

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

GeneralForcePrecision now chooses a monotone precision q_j with
`e_(q_j)<E0/2^j` from the proved error-vanishing contract. E0>0 is an explicit
acceleration precision scale. GeneralForceEndpoint constructs fixed-time names
from actual level-j central schedules at q_j. Under global approximate
Lipschitz comparison, the calibrated window and uniform bounds B at actual
coarse and first-half shadow arrivals, coarse speed is derived as
`V=|v0|+TB`. The weighted adjacent bound is

    T*h*C + 7*τ₀*T*E,  h=T/2^(j+1), E=3*e_(q_j),
    C=B+τ₀*L*(V+TB).

Equivalent duration values require a separate actual sample-error comparison;
rounded maps need not agree at equal-valued point representations. The checked
control in EquivalentDuration detects omission of this term. Hence the derived
geometric coefficient is `T²*C+42*τ₀*T*E0`. Shared geometric tails then construct
the motion name and value, without a supplied adjacent/Cauchy motion estimate.
Zero time is included. HarmonicGeneralEndpoint derives its actual/shadow B on
the short family and proves that these general names/values equal the retained
harmonic endpoint construction. It does not assert a global harmonic force
bound. The global-comparison version does not yet supply the confined-annulus
comparison theorem, a full general time map, restart/gluing or P5.

For merely continuous fields, existence (possibly by a subsequence),
full-sequence convergence and uniqueness are separate obligations. They will
not be replaced by a structure field asserting the desired trajectory.

## Actual finite accumulation and continuous consistency

`BoundedIteration.run` constructs the actual triangular iterates. Under bounded
arrival samples, velocity is at most `|v₀|+TB`, and position is at most
`|x₀|+T|v₀|+T²B`, uniformly over meshes with elapsed time at most T.
`ForceClasses.run_eq_schedule` and the `sampled_polygon_*_bound` theorems
identify these with the mechanical schedules. `BoundedOn` and membership of
every arrival in the region are explicit premises. They apply to bounded
continuous (b)/(c), and even bounded (d), without deriving convergence.

`FiniteAccumulation` constructs actual full-cell and two-half-cell iterates
and derives their finite error recurrence. On `T=2nh`, `T(1+L) ≤ 1/2`, its
finite product bound gives `D_n ≤ 2n S`, where S includes both the actual
local defect and propagated additive sample error. B bounds first-half samples
and V coarse velocities only for `k<n`. The global comparison contract also
covers comparison locations that are not vertices of the coarse polygon;
a region-local replacement must prove those locations confined. See the
[accumulation verification](verification/general-accumulation-2026-10-04.md).
The cross-map theorem compares different fine and coarse rational samples;
`sampled_uniform_refinement` instantiates it at precisions j+1 and j with
the derived discrepancy `3e_j`, under its explicit global-region premise.

`sample_point_error` transfers oracle coherence to point distance, and
`samples_comparison_contract` derives a cross-precision global force contract
with discrepancy `3e_i` for `i≤j` when the declared region contains every
rational point. It does not treat rounded sample maps as exactly Lipschitz.
For a confined annulus, only the local version of this contract applies.

`continuous_local_refinement` derives, for each positive eps, a positive delta
and precision N from `ContinuousOn`. If the three actual sample locations lie
in the region and their drift/refinement separations are below delta, the
local state defect is bounded by `|h²|B+|h|(eps+eps)`. No Lipschitz coefficient
is substituted for continuity. This controls the local source; a stability
or subsequence construction and uniqueness require separate arguments.
