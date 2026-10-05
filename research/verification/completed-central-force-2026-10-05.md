# Completed central force, 5 October 2026

Root Sol 6.1 implementation, continuing B.3 after the committed dyadic
position-secants bridge ee889fe. This is a modern reconstruction with no new
historical edge. De Motu, 1687 and 1713 remain separate.

SampledValues completes a family of rational map samples. Its data contain
ordered finite comparisons with nonnegative coefficient and additive error,
and positive-tolerance error exhaustion. They contain no completed map,
Cauchy field for the input motion, continuity assertion or desired force
equation. Diagonal samples at each Cauchy approximant are proved Cauchy.
Name-equivalence preservation precedes the quotient lift. Vanishing-error and
affine transfer give the completed Lipschitz and actual sample bounds.

CompletedForce uses the same monotone precision q_j as the actual motion.
Oracle coherence and approximate Lipschitz comparison derive coefficient L
and error 3*e(q_j). The extension depends only on position and is a completed
planar value, with zero velocity slots. It agrees with the retained force at
rational points and is independent of the precision scale E0 and the valid
Lipschitz bound. The proof permits constant precision for zero-error oracles;
no q_j>=j premise is used. Motion precision independence remains open.

Actual prefix force samples satisfy

    Within(sample_j(prefix_j), forceValue(gamma(t)),
           (A*L+3*E0)/2^j),

where A is the already derived prefix coefficient. Rational exhaustion proves
uniform convergence over all binary addresses. The global-region premise is
explicit; annular confinement is not supplied by continuity. The harmonic
specialization equals completed scaling by -w at every completed position,
independently of representative and precision, and gives the retained-curve
uniform sample result. These exact specialization and rational-agreement
theorems are disclosed proof controls, not independent numerical oracles.

Acceleration/secant identification and unrestricted differentiation remain
open. No derivative, integral, ODE, potential asymptotic, ordinary-area or
Kepler-area theorem is asserted. Generic ingredients live in BarrowLib.
The editorial estimate stays 38.03%: the force extension is an ingredient of
the next identification bridge, with no separate credit for helper count.

Targeted Lean 4.19 core builds and all 16 sequential checklist commands pass.
A nonauthor GPT-6 Luna verifier confirmed all 1,685 prior public names and
signatures, with 31 new names. The catalogue has 1,352 distinct rows and 1,212
references; live counts are 980 substantive, 195 plumbing, 151 sample and 26
duplicate. All 21 new rows and all 552 Barrow rows are source-free. The axiom
union is propext, Classical.choice and Quot.sound, with no sorryAx, project
axiom or external dependency. The graph remains 77/68/249. Logs:
/tmp/newton-sol61-completed-force-final-01.log through -16.log. Root Sol 6.1
commits the verified increment; the unrelated archive edits are preserved.
