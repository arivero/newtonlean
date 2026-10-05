# Constructed dyadic velocity secants, 5 October 2026

Task B.3's first constructed-rate increment identifies velocity through
position differences of actual completed curve endpoints. Its exact statement
is GeneralForceSecants.dyadic_velocity_uniform_identification:
given the proved general local map's conditions and T>0, for every eps>0 there
is N such that, for every m>=N and every binary address b, the completed secant
across the level-m cell bracketing b lies Within eps of the constructed velocity
at b. The final cell uses the actual right endpoint. No velocity identity,
derivative, curve, limit point or rate bound is supplied as a structure field.

KinematicEstimates proves finite velocity displacement <=t*B and position
remainder from its initial inertial continuation <=t²*B. The positive-time
secant error is <=t*B. These use actual recursive drift/kick runs and bounds
on their sampled arrivals, without a Lipschitz or continuity hypothesis.
BoundedIteration transports the actual arrival bounds under finite restart.
Equivalent represented elapsed times have the same rational quotient estimate.
A two-cell constant parallel-force control has exact quotient error 1/4 and
rejects the deliberately omitted zero bound. These are disclosed exact proof
controls, not independent computed oracles.

SecantValues constructs rationally scaled position-difference Cauchy names and
velocity projections, proves name-equivalence transport, and then lifts them
to values. DyadicNodes derives later cell counts, durations and actual node
time coordinates, including the right endpoint. Time truncation lies Within
H_m=T/2^m of its original time value. Finite name shifts preserve values.

GeneralForceSecants.nodeName realizes the existing constructed map at each
node; it is not a different motion. Fine actual run remainders at every level
pass to the completed cell secant and give distance <=H_m*B from its left-node
velocity. The map's derived time bound adds H_m*K from that velocity to the
target velocity, where

    V = |v0|+T*B,
    K = (1+1/tau)*(V+tau*B).

Thus the uniform completed secant error is at most H_m*(B+K), which tends
to zero by rational exhaustion. HarmonicSecants applies the result to the
retained harmonic gammaValue: all actual force bounds are derived, and
HarmonicGeneralTime already identifies the maps exactly. The general completed
map still has explicit global Lipschitz comparison, a calibrated window and
actual/coarse/shadow sample premises; confinement is not derived.

This is the dyadic bracketing secant criterion on the constructed binary-time
domain. Unrestricted difference-quotient differentiation, external real-time
identification and acceleration identification with completed sampled force
remain open. Curved potential asymptotics, general whole-edge/content extension,
ordinary/Kepler-area identification, annular confinement, gluing and arbitrary-
partition independence also remain open. Generic ingredients belong to
BarrowLib; no derivative, integral, ODE primitive or external package is used.
No historical edge is added; De Motu, 1687 and 1713 remain separate.

The editorial identification score rises from 0.20 to 0.25 for this completed-
curve rate bridge, with no credit for helper count or migration. No target is
discharged. Targeted Lean 4.19 core builds and all 16 sequential checklist
commands pass. A nonauthor GPT-6 Luna verifier confirmed all 1,632 prior public
names/signatures, with 53 new names. The catalogue has 1,331 rows, 1,191
references, 968 substantive results and 544 source-free Barrow rows. The axiom
union is propext, Classical.choice and Quot.sound. Logs:
/tmp/newton-sol61-velocity-secants-final-01.log through -16.log; the full record
is in VERIFICATION.md. Root Sol 6.1 commits the verified increment.
