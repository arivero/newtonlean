# General constructed tangent triangle, 5 October 2026

Root Sol 6.1, handoff C.2 after fd1f45a. All new results are source-free modern
reconstructions; De Motu, 1687 and 1713 remain separate.

TangentTriangleValues constructs the signed doubled determinant of the sides
c-B and C-c, where B is the completed left point, c its tangent continuation
with constructed velocity, and C the completed right point. Existing secant
and pairing operators supply the Cauchy and representative proofs. The rational
embedding is exactly triangleTwice B c C. For every positive rational H and
arbitrary completed endpoints, the exact normalized identity is

    triangle/H³ = det(v_left,z_left)/2,
    z_left = 2/H*((C-B)/H-v_left).

It assumes no curve expansion. PairingValues now transfers a closed bound in
one input while the other input name has a proved bounded tail.
GeneralForceTangentTriangle supplies actual node velocity bounds V=|v0|+T*B
and the already proved second-order comparison: z_left lies within 2*L*H*V
of the completed force at B. Determinant comparison and the outer half give
normalized triangle error at most H*L*V². Rational exhaustion proves uniform
convergence over all cells, including the cell ending at the full endpoint.
Force sampling and half-mesh errors were already exhausted by the reused
second-order bridge; their proof is not copied into the new triangle client.

The explicit hypotheses are the same sampled inward central-force oracle,
global approximate Lipschitz comparison, positive calibration and time,
calibrated short window and actual/coarse/shadow sample bounds. The result
applies to the existing Lipschitz construction and its harmonic specialization;
it does not assert motion existence for all merely continuous central laws.

The output is signed doubled tangent area. Reading unsigned triangle area as
half the absolute doubled determinant gives coefficient |v cross a|/4.
No ordinary area of a lobe or matched region is inferred. General radial
potentials and their curved steps, D_mesh/lobe identification, unrestricted
quotients, external real time, confinement/gluing, general interior-time E/G
and the remaining force classes stay open. Scores remain 38.59% overall
(35.16-46.30%), Prop I 61.25%; seven heuristic-substantive rows are not seven
completed obligations.

Targeted Lean 4.19 core compilation and All 16 sequential checklist commands pass, including the default and both
explicit library builds, catalogue/reference and standard-axiom inspection,
source/graph, rendering, hashes and whitespace. The catalogue has 1,476 distinct
rows and 1,332 emitted reference checks; live heuristic counts are 1,094
substantive, 197 plumbing, 159 sample and 26 duplicate. All seven new rows
and all 617 Barrow rows are source-free modern reconstructions. All 1,884 prior
public names/signatures at fd1f45a remain unchanged, with ten new names (bounded
source inventory plus kernel compilation). The graph remains 77/68/249; the
axiom union is propext, Classical.choice and Quot.sound, with no sorryAx,
project axiom, external package or Newton/Mathlib foundation import. Graph PDF
dates are restored only after proving all other bytes unchanged. Logs:
/tmp/newton-sol61-general-triangle-final-01.log through -16.log; API audit:
/tmp/newton-sol61-general-triangle-api.json. Root Sol 6.1 commits the verified
increment, preserving unrelated conversation archives.
