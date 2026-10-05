# Constructed harmonic potential increments, 5 October 2026

Root Sol 6.1, handoff C.2 after fe732e4. All new results are source-free modern
reconstructions; De Motu, 1687 and 1713 remain separate. This constructs the
harmonic potential values at actual curve points and derives the dyadic leading
potential increment, without assuming a Taylor formula or the desired expansion.

PairingValues shares one Cauchy and representative-independence argument for
dot products and determinants. Their finite bilinear differences and L1
magnitude bounds control errors. Position boundedness on a Cauchy tail is
proved once; the old mesh-product proof now reuses it. QuadraticPotentialValues
composes these pairings and the existing completed secants, constructing
c*dot(p,p), the tangent continuation and the normalized potential increment.
Its rational embedding identity agrees with the polynomial. No nonlinear
completion is duplicated per force law.

For the actual retained harmonic curve, take c=mass*w/2 and a(p)=-w*p. The
finite work identity is

    V(q)-V(p)+mass*a(p) dot (q-p) = c*dot(q-p,q-p).

This identifies the polynomial potential with the force without a derivative
primitive. The actual general finite node-second estimate is extracted once:
both its previous completed force bridge and this potential client use the
same restarted-run proof. No old declaration statement changes.

Let H=T/2^m, P=2*stateNorm(s0), B=|w|*4*stateNorm(s0),
V=|v0|+T*B, A=|w|*P, U=2*|w|*V, and Z=2*A+T*U. Actual node
approximants satisfy the P/V bounds. Their normalized second departure z_j
satisfies |z_j-a_left_j| <= H*U+2^-j*A and |z_j| <= Z. Finite polynomial
algebra therefore gives normalized potential error at most

    H*C+2^-j*Q,
    C=|c|*(P*U+Z*V+(T/4)*Z²), Q=|c|*P*A.

All bounds and nonnegativity are derived. The rounding term vanishes only after
passing through the closed comparison of the constructed Cauchy names. The
remaining H*C bound gives uniform convergence, over every dyadic cell including
the last one, of

    [V(gamma_right)-V(gamma_left+H*v_left)]/H²

against the completed value -mass*dot(a_left,a_left)/2. Dot is the Euclidean
squared magnitude here, distinct from the L1 gauge used to bound errors. The
hypotheses are w>=0, T>0 and the retained calibrated harmonic short window
T*(1+|w|)<=1/2. Mass is any rational parameter; physical nonnegative mass is
included. This is a leading result along constructed dyadic cells, not an
unrestricted derivative or an external-real-time theorem.

The finite quadratic prediction control at mass=w=1, h=1/2, B=(1,0), v=(0,1)
has exact potential drop -15/128, versus leading -1/8. It refutes finite exact
identification even for a quadratic predictor. This is a rational polynomial
proof control, not an independently computed harmonic orbit.

General radial potentials and their curved steps, the tangent-triangle/lobe
relation to D_mesh, ordinary/inner area and Kepler transfer, unrestricted
quotients, confinement/gluing, general interior-time E/G and the remaining
force classes stay open. Scores remain 38.59% overall (35.16-46.30%), Prop I
61.25%; this individual law test receives no independent count credit.

Targeted Lean 4.19 core compilation and All 16 sequential checklist commands pass, including the default and both
explicit library builds, catalogue/reference and axiom inspection, source/graph,
rendering, hashes and whitespace. The catalogue has 1,469 distinct rows and
1,325 emitted reference checks; live heuristic counts are 1,087 substantive,
197 plumbing, 159 sample and 26 duplicate. All 26 new rows and all 613 Barrow
rows are source-free modern reconstructions. All 1,844 prior public names and
signatures at fe732e4 are preserved, with 40 new names (bounded source-reader
inventory plus kernel compilation). The graph remains 77/68/249; the axiom
union is propext, Classical.choice and Quot.sound, with no sorryAx, project
axiom, external package or Newton/Mathlib foundation import. Graph PDF dates
are restored only after proving all other bytes unchanged. Logs:
/tmp/newton-sol61-constructed-potential-final-01.log through -16.log; API audit:
/tmp/newton-sol61-constructed-potential-api.json. Root Sol 6.1 commits the
verified increment; unrelated conversation archives are preserved.
