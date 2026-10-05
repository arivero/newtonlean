# Finite quadratic control and constructed parallel endpoints, 5 October 2026

Root Sol 6.1, handoff C.2 following be2d00e. Source-free modern reconstruction;
De Motu, 1687 and 1713 remain separate. This is a bounded law test and the
finite mechanism for the general central second-order bridge.

QuadraticEstimates derives the exact actual constant-map run

    x_n = x0+t*v0+t*(t-h)*a/2,    v_n = v0+t*a,    t=n*h.

Actual force variation bounded by C gives a position remainder at most t²*C
against this discrete predictor. The approximate Lipschitz comparison and
actual velocity cap derive C=L*t*V+E. The discrete predictor differs from
x0+t*v0+t²*a/2 by exactly t*h*|a(x0)|/2 in the coordinate L1 gauge. The mesh
term is retained explicitly. A two-cell parallel control has distance 1/4 and
rejects exact finite equality with the continuous quadratic predictor. These
controls are rational arithmetic proofs, not independent numerical checks.

ParallelQuadraticEndpoint uses actual constant-force runs with 2^j cells of
duration T/2^j. Represented elapsed time equals T. Its exact full-state error
from the quadratic state is C0/2^j, C0=T²*|a|/2; velocity error is zero. This
derived estimate proves the actual endpoint Cauchy condition and identifies
the completed value with the quadratic state, at every nonnegative rational
time, including zero and without a small-window or supplied-curve premise.

QuadraticEndpointPotential identifies C with that actual completed Galilean
endpoint before deriving its tangent-deflection triangle and linear-potential
drop. Doubled signed area is t³*det(v,a)/2 and ΔV=-m*g²*t²/2. The division-
free identity m*g*doubled_area=t*v_x*ΔV remains exact: both coefficients
halve, leaving the motion-dependent time ratio v_x/(2g). Neither this triangle
nor the finite kick triangle is the matched-region D_mesh or a chord–arc lobe.

This constructs rational-time parallel endpoint values, not a parallel map at
arbitrary binary times. General central completed second-order/potential
estimates, ordinary-area/Kepler-area identification, D_mesh proportionality,
partition independence, confinement/gluing and the other force classes remain
open. No derivative, integral, ODE, potential-existence axiom, mathlib or quantum
premise is imported. The existing score remains 38.59% (35.16–46.30%), Prop I
61.25%; helpers and this individual-law test receive no extra credit.

Targeted Lean 4.19 core compilation and all 16 sequential checklist commands
pass, including all three builds, references/axioms, evidence and rendering,
hashes and whitespace checks. All 1,802 prior public names/signatures at
be2d00e remain unchanged, with 27 new names. The catalogue contains 1,432
distinct rows and 1,292 references; live categories are 1,054 substantive,
195 plumbing, 157 sample and 26 duplicate. All 19 new rows and all 591
Barrow rows are source-free. The graph remains 77/68/249 and the axiom union
is propext, Classical.choice and Quot.sound, with no sorryAx, project axioms
or external package. Logs: /tmp/newton-sol61-quadratic-parallel-final-01.log
through -16.log. Root Sol 6.1 commits the verified increment and preserves
unrelated conversation archives.
