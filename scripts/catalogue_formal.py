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
