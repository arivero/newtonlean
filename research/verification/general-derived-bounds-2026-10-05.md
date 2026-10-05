# Derived general force bounds, 5 October 2026

Root Sol 6.1, current increment after 2b98a36. All new mathematical rows are
source-free modern reconstructions. De Motu, 1687 and 1713 remain separate.

CalibratedGrowth assumes the finite growth contract |a(p)|<=L|p|+E. It reuses
TimeCalibration.component_amplification and the existing finite power/source
budgets to derive |x_n|+tau|v_n|<=M=2*(r0+tau*T*E), where
r0=|x0|+tau|v0| and T*(1/tau+tau*L)<=1/2. Its length cap is invariant under a
positive time-unit change, including E's acceleration-unit rescaling. No ODE,
integral inequality, arrival bound or confined curve is a premise.

ForceClasses derives vanishing of inward samples at the origin and linear
growth from the whole-plane approximate Lipschitz comparison. Chosen precision
bounds sample error by E0, so E=2*E0 works uniformly in the mesh level.
GeneralForceGrowth bounds actual and doubled-half-mesh runs by M. Its shadow
arrival has position magnitude at most R=M+T*M/tau. B=L*R+E therefore supplies
all three actual/coarse/shadow sample fields of the retained prefix conditions.
The initial state and force data compute B; no bound along a desired motion is
supplied. Every existing motion, secant, polygon and region client can consume
these conditions. The old conditional APIs and harmonic constructions remain.

This increment retains global_region. It does not apply to forces singular at
the centre, including Kepler 1/r^2. The revised handoff requires A.6 region
confinement with that instance next, before other new work. Constructed-curve
area law, general radial potentials, ordinary/inner area, D_mesh/lobe relation,
external real time, partition independence, gluing and historical completion
remain separate. Scores stay at 38.59% overall (35.16-46.30%) and Prop I 61.25%.

Targeted Lean 4.19 core compilation passes. All 16 sequential checklist commands
pass, including the default and both
explicit library builds, catalogue/reference and standard-axiom inspection,
source/graph, rendering, hash and whitespace checks. There are 1,347 emitted
reference checks; the graph has 77 nodes, 68 edges and 253 passages. The
axiom union is propext, Classical.choice and Quot.sound, with no sorryAx,
project axiom, external package or Newton/Mathlib foundation import. PDF
dates were restored only after proving all other bytes unchanged. Logs:
/tmp/newton-sol61-derived-bounds-final-01.log through -16.log.
The live catalogue has 1,491 distinct rows, including 625 Barrow rows;
heuristic counts are 1,106 substantive, 197 plumbing, 162 sample and 26 duplicate.
The sample category includes universal sampled bounds, so it is not a research
milestone count. All 1,894 prior public names/signatures at 2b98a36 are preserved,
with 21 new names and 15 new theorem rows. The source inventory is not a Lean
parser; kernel compilation supplies the proof verification. API audit:
/tmp/newton-sol61-derived-bounds-api.json. Unrelated conversation archives are
preserved and excluded from staging.
