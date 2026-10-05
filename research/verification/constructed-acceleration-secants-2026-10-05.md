# Constructed acceleration secants, 5 October 2026

Root Sol 6.1 implementation, B.3 following ee889fe and 9931c3d. This is a
modern reconstruction, source-free. De Motu, 1687 and 1713 remain separate.

AccelerationEstimates derives actual position displacement from bounded
preceding velocities, then force variation from the approximate Lipschitz
comparison. The finite velocity remainder against v0+t*a(x0) is at most
t*(L*t*V+E). Dividing by the positive elapsed time gives quotient error
L*t*V+E; equivalent rational elapsed-time representations are covered. An
exact two-cell negative identity-map control has finite error 1/8 and rejects
the false zero bound. These are disclosed rational proof controls, not
independent numerical oracles.

SampledValues proves that a finite precision offset preserves its completed
map, and transfers a proved vanishing additive error to a closed completed
bound. GeneralForceAccelerationSecants applies these to the actual restarted
fine schedules between the two dyadic nodes of the existing constructed map.
The fine time is represented as the coarse cell duration H_m. Global velocity
V=|v0|+T*B is derived from the actual full-grid sample bounds. Every force
comparison uses actual arrivals. The finite 3e(q_(m+j)) term vanishes in the
completed comparison; it is not discarded before that step.

The completed cell velocity secant lies Within L*H_m*V of the completed force
at its left node. Lipschitz force control and derived time truncation give

    Within(cellAccelerationSecant_m(t), forceValue(gamma(t)),
           H_m*L*(V+K)),

where K is the existing explicit-calibration stateTimeFactor. Rational
exhaustion proves uniform convergence over every binary address, including
the final boundary. The force is the same completed extension constructed in
9931c3d, by precision-offset invariance. The motion and both completed secant
operators were constructed first; no desired acceleration equation is supplied.
HarmonicAccelerationSecants proves the retained-curve corollary, with completed
force exactly the scalar -w operator and all sample bounds derived.

The theorem gives the completed bracketing dyadic velocity-secant criterion.
Unrestricted difference quotients and external real-time identification remain
separate. Globally compared Lipschitz data, a calibrated short window and
actual/coarse/shadow force bounds are explicit; annular confinement, gluing,
motion precision/partition independence, ordinary-area/Kepler-area transfer and
curved potential estimates remain open. No derivative, integral, ODE, external
package or later mechanical premise is imported.

Identification rises from 0.25 to 0.30 for this acceleration/force bridge,
without helper-count credit: 38.31% overall, range 34.94–46.08%, Prop I 60%.
Targeted Lean 4.19 core builds and all 16 sequential checklist commands pass.
A nonauthor GPT-6 Luna verifier confirmed all 1,716 prior public names/signatures
at 9931c3d, with 25 new names. The catalogue has 1,371 distinct rows and 1,231
references; live counts are 995 substantive, 195 plumbing, 155 sample and 26
duplicate. All 19 new rows and all 565 Barrow rows are source-free. The axiom
union is propext, Classical.choice and Quot.sound, with no sorryAx, project
axiom or external package. The graph remains 77/68/249. Logs:
/tmp/newton-sol61-acceleration-secants-final-01.log through -16.log.
Root Sol 6.1 commits the verified increment; unrelated archives are preserved.
