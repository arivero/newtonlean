# Explicit time calibration in finite force estimates, 5 October 2026

Task A's units amendment is implemented as a modern elementary reconstruction.
No passage or dependency is added to De Motu, 1687 or 1713. The retained τ₀=1
formulas remain available with unchanged public names/signatures.

For positive rational τ₀, TimeCalibration constructs |x|+τ₀|v| and the
corresponding weighted distance. Its actual triangular-cell bound is

    D_next ≤ K D + τ₀|h|E,
    K=(1+|h|/τ₀)(1+τ₀|h|L)=1+|h|(1/τ₀+τ₀L)+h²L.

A shared finite pair-factor proof gives K^n≤2 when
n|h|(1/τ₀+τ₀L)≤1/2. The retained coarse/two-half unit-gauge proof instantiates
this same theorem. Actual two-map n-cell iterates from the same state satisfy
D_n≤2nτ₀|h|E. No motion error, desired convergence or limit point is a supplied
premise. The force comparison contract and nonnegative L,E are explicit.
Newton-side wrappers instantiate it for different oracle precisions, the
harmonic field and the permitted constant parallel field.

For c>0, h→ch, τ₀→cτ₀, v→v/c, L→L/c² and E→E/c² preserve the weighted gauge,
distances, K, its window and sampling source. The same coordinate family's
Cauchy condition is equivalent in every fixed positive calibration. Rescaled
families have the corresponding same Cauchy condition. Exact harmonic cell
mechanics commute with this unit change. This is not an assumed covariance of
an arbitrary rounded sample map under value-equivalent arrival coordinates.

Production controls check a factor-three rescaling and L=0, and detect that
omitting τ₀ changes the unweighted norm under a velocity rescaling. τ₀ is free
data. It supplies no positive universal action constant or value for Planck's
constant. The square-root dynamical time is an interpretation of L's units,
not a rational-square-root primitive imported into Lean.

Root Sol 6.1 implemented the bounded increment. A sequential nonauthor GPT-6
Luna verifier passed all 16 checklist commands in order. There are 1,074 unique
theorem rows (731 substantive, 186 plumbing, 136 sample, 21 duplicate), 932
emitted references and 377 source-free Barrow rows. Every previous public name
and signature is preserved. The standard axiom union is propext, Classical.choice,
Quot.sound; no sorryAx or project axiom. Logs:
/tmp/newton-sol61-calibration-final-01.log through -16.log. VERIFICATION.md
records the full result. The packages are
empty and the foundation imports no Newton-specific module. General force
trajectory construction, confinement/restart, actual between-path content,
P5 and leading curve/potential asymptotics remain separate obligations.
Completion scores are unchanged.
