"""Inventory checked declarations and preserve their actual premise signatures.
The file-level source correspondence is a locator, not a claim of historical proof.
"""
import json
import re
from pathlib import Path
root = Path(__file__).resolve().parents[1]
correspondence = {
 'Common/Quadratic.lean': ([], 'Logical reconstruction of eventual enclosure; all Magnitudes fields are parameters.'),
 'Common/RationalMagnitudes.lean': (['NATP00077.par26','NATP00082.par27'], 'Rational consistency model and arithmetic support, not full Euclidean geometry; triangle limit still requires a slope limit.'),
 'DeMotu1684/QuadraticDeflection.lean': (['RSreprint.H4'], 'Initial-ratio predicate only; not a proof of the manuscript hypothesis.'),
 'Principia1687/LemmaX.lean': (['NATP00077.par28'], 'Legacy conditional squeeze: supplied triangle limits and mechanical velocity-area identification.'),
 'Principia1687/ConstructedRatio.lean': (['NATP00077.par26','NATP00077.par28'], 'Constructed ratio and triangle cancellation; contact limits, mechanical enclosure and positive coefficient remain premises.'),
 'Principia1713/LemmaX.lean': (['NATP00082.par29'], 'Shared conditional geometry, not identification of edition-specific mechanical hypotheses.'),
 'Principia1713/ForceComparison.lean': (['NATP00082.par32','NATP00082.par33','NATP00082.par34'], 'Exact coefficient algebra only; common calibration, comparable force and positive denominators. Variable-force initial comparison not proved.'),
 'Polygon/Finite.lean': (['NATP00089.par9','NATP00090.par17','NATP00077.par45','NATP00082.par51'], 'Synthetic Euclidean area identities are imported; integer-coordinate instance is proved. No limiting trajectory.'),
 'Polygon/Enclosure.lean': (['NATP00077.par6','NATP00082.par7','NATP00077.par45','NATP00082.par51'], 'Rectangle arithmetic is proved. Curve enclosure, vanishing budget and inner/outer ratio limits are supplied where present in the signature.'),
 'Polygon/Contact.lean': (['NATP00089.par9','NATP00090.par17','NATP00077.par45','NATP00082.par51'], 'Modern diagnostic of the finite polygon construction: restart of the actual recurrence, endpoint contact, discrete velocity jumps, and an inward lattice nonidentification example. The passages locate the motivation only; they do not attribute this interface or its counterexample to Newton, and no continuous trajectory follows.'),
 'Polygon/RefinementStrip.lean': (['NATP00089.par9','NATP00090.par17','NATP00077.par45','NATP00082.par51'], 'Modern finite coordinate diagnostic motivated by the polygon constructions: exact Euclidean triangle area between a coarse edge and a compatible one-cell refinement. The passages locate motivation only; no limiting curve, common-force time refinement, integration, or trajectory existence is attributed or inferred.'),
 'Polygon/TimeSubdivision.lean': (['NATP00089.par9','NATP00090.par17','NATP00077.par45','NATP00082.par51'], 'Modern finite coordinate diagnostic: an explicitly scheduled constant-acceleration end-kick coarse/fine comparison over positive rational durations. It proves a non-nested endpoint mismatch and closes the resulting finite boundary by a connector. The passages locate motivation only; no limiting curve, integration, trajectory existence, or Newtonian general central-force theorem is attributed or inferred.'),
 'Polygon/PartitionControl.lean': (['NATP00089.par9','NATP00090.par17','NATP00077.par45','NATP00082.par51'], 'Modern finite bookkeeping for arbitrary common-denominator end-kick schedules. The actual `partitionMotion` is the repeated `TimeSubdivision.endKick` recurrence; its exact candidate residual is `(Q/(2*D^2))*a`, with a nonnegative coefficient bounded by the maximum-cell coefficient. This is a rational-time candidate formula only: no convergence, limiting curve, integration, trajectory existence, or Newtonian general central-force theorem is attributed or inferred.'),
 'Polygon/PartialCell.lean': (['NATP00089.par9','NATP00090.par17','NATP00077.par45','NATP00082.par51'], 'Modern finite bookkeeping for a partial final end-kick cell of duration `u/D` after an actual common-denominator prefix. The partial position is the drift of the actual prefix state and equals the appended schedule `weights ++ [u]`; the exact candidate residual `((Q+u*u)/(2*D^2))*a` and the within-cell bound `Q+u*u <= M*(T+u)` for `u <= w <= M` are derived from the appended statistics. Boundaries u=0, u=w and a=0 are corollaries. Rational-time positions only: no convergence, limiting curve, integration, trajectory existence, or Newtonian general central-force theorem is attributed or inferred.'),
 'Polygon/UniformRefinement.lean': (['NATP00089.par9','NATP00090.par17','NATP00077.par45','NATP00082.par51'], 'Modern finite estimate: for each positive rational tolerance and rational time `N/E`, an explicit uniform refinement (`K = N*den+1` unit cells over `E*K`) reaches the same time with constant-force residual coefficient `Q/(2D^2)` at most the tolerance. It is one refinement per tolerance, with no sequence limit, Cauchy comparison of arbitrary partitions, Euclidean-time trajectory, or central-force theorem inferred.'),
 'Polygon/PartitionComparison.lean': (['NATP00089.par9','NATP00090.par17','NATP00077.par45','NATP00082.par51'], 'Modern finite comparison: two arbitrary common-denominator end-kick schedules reaching equivalent rational times have actual positions that agree after each is corrected by its own exact residual `(Q/(2*D^2))*a`; the candidate respects rational time equivalence. With the mesh bounds this controls partition dependence along `a`. No limit, Euclidean-time trajectory, or central-force theorem is inferred.'),
 'Polygon/ZeroForce.lean': (['NATP00076.par1','NATP00081.par1','NATP00090.par5'], 'Modern rational coordinate reconstruction of zero impressed acceleration. The actual end-kick recurrence agrees with `p + t*v` at every finite rational schedule time, including rest, exact restart, and equivalent times across denominators. The locators motivate the inertial premise only; NATP00089.par4 is a deleted supporting witness and is not a surviving premise. No all-Euclidean-time trajectory, limiting curve, or historical proof dependency is inferred.'),
 'Polygon/InertialControl.lean': (['NATP00076.par1','NATP00081.par1','NATP00090.par5'], 'Modern rational small-time estimate for zero impressed acceleration. An explicit positive radius controls both coordinate drifts for every rational base time and an actual zero-force end-kick cell. It is a finite algebraic estimate, not an all-Euclidean-time trajectory, curve existence theorem, or historical proof dependency.'),
 'Polygon/InertialDefect.lean': (['NATP00076.par1','NATP00081.par1','NATP00090.par5'], 'Modern rational coordinate identity for zero impressed acceleration: directed determinants of samples on one inertial line compose additively, so every finite closed walk, including its explicit connector, has zero signed doubled area; four actual zero-force schedules with different partitions give a vanishing boundary. Signed sums only; no unsigned enclosure estimate, timing identification, continuum curve, or historical proof dependency is inferred.'),
 'Diagnostic/InverseCubeAreal.lean': (['NATP00077.par62','NATP00082.par73','NATP00082.par79'], 'Action diagnostic layer, not a historical proof: natural-number magnitudes of two uniform circles compared through the Proposition IV Cor. 1 proportion. An inverse-cube comparison is equivalent to equal squared areal velocity; an inverse-square instance has unequal areal velocities. The general power-law Cor. 7 is 1713 only. Supports research/action-arguments Arg002; it fixes a system-dependent action and gives no universal constant.'),
 'Contact/Bounds.lean': (['NATP00077.par32','NATP00077.par37','NATP00082.par37','NATP00082.par44'], 'Circle identity and positive diameter lower bound, or quadratic departure and rectangle enclosure, are explicit premises; no curved configuration is constructed.'),
 'Contact/FiniteSums.lean': (['NATP00077.par37','NATP00082.par44'], 'Finite arithmetic and modern bookkeeping of a uniform error budget. Not a historical N^-2 theorem; the geometric coefficient identification is separately checked in AreaCoefficient.lean.'),
 'Contact/AreaCoefficient.lean': (['NATP00077.par28','NATP00077.par37','NATP00082.par29','NATP00082.par44'], 'Normalized linear/parabolic coefficients and scaled constant-force example from all finite rectangle enclosures; geometric enclosure and mechanical area identification remain distinct premises.'),
 'Comparison/Routes.lean': (['NATP00082.par91','NATP00087.par89'], 'Constant-force coordinate example and matched-duration algebra; general orbit correspondence remains conditional.'),
}
results=[]
for path in sorted((root/'NewtonLimitDynamics').rglob('*.lean')):
    rel=str(path.relative_to(root/'NewtonLimitDynamics'))
    sources,note=correspondence[rel]
    text=path.read_text()
    namespace=[]
    for line in text.splitlines():
        if line.startswith('namespace '): namespace.append(line.split()[1])
        if line.startswith('end ') or line == 'end': namespace.pop()
        match=re.match(r'(private )?theorem (\w+)',line)
        if match:
            local=match[2]
            header=re.search(r'(?:private )?theorem '+re.escape(local)+r'\b([\s\S]*?):=',text)
            assert header, (path,local)
            results.append({'name':'.'.join(namespace+[local]),'private':bool(match[1]),
                'file':str(path.relative_to(root)),'source_passages':sources,
                'classification':'modern_reconstruction','premise_signature':header[1].strip(),
                'interpretation_and_remaining_premises':note})
(root/'research/formal-results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
print(f'Inventoried {len(results)} theorems with signatures and source boundaries')
