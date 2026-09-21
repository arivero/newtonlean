"""Generate a bounded comparison from explicit passage alignments and edges.
Absent ledger edges are NOT declared absent from an entire edition.
"""
import json
from pathlib import Path
root = Path(__file__).resolve().parents[1]
rows = json.loads((root/'research/edition-alignments.json').read_text())
passages = {p['id']: p for p in json.loads((root/'research/passages.json').read_text())}
data = json.loads((root/'research/dependencies.json').read_text())
text = '# Supported edition comparison\n\nGenerated from edition-alignments.json and dependencies.json. Coverage is the selected chain, not whole editions. Proposed numbers never identify actual-edition propositions.\n\n'
text += '| Item | 1687 | 1713 | 1726 | Supported change |\n| --- | --- | --- | --- | --- |\n'
for r in rows:
    cells = []
    for stage in ['1687','1713','1726']:
        refs = r['passages'].get(stage, [])
        assert refs, (r['item'],stage)
        assert all(x in passages and passages[x]['stage'] == stage for x in refs)
        cells.append(', '.join(f'[{x}]({passages[x]["url"]})' for x in refs))
    text += '| '+r['item']+' | '+' | '.join(cells)+' | '+r['change']+' |\n'
text += '\n## Recorded incoming dependencies of Proposition VI\n\nOnly the cited proof paragraphs are compared; an absent edge here is not a claim of global logical independence.\n\n'
for stage in ['1687','1713','1726']:
    text += f'- {stage}: '
    edges = [e for e in data['edges'] if e['relation']=='proof_dependency' and e['to']==f'P{stage}.P6']
    text += '; '.join(f'{e["from"]} ({e["status"]}; {e["passage"]})' for e in edges)+'.\n'
for old,new in [('1687','1713'),('1713','1726')]:
    get = lambda stage: {e['from'].split('.',1)[1] for e in data['edges'] if e['relation']=='proof_dependency' and e['to']==f'P{stage}.P6'}
    a,b=get(old),get(new)
    text += f'\n{old} → {new}, recorded incoming labels: added {", ".join(sorted(b-a)) or "none"}; removed {", ".join(sorted(a-b)) or "none"}. '
    text += 'This records the new proof organization; the generated-motion alternative is retained through Lemma X corollary 4.\n'
(root/'research/edition-comparison.md').write_text(text)
print(f'Validated and generated {len(rows)} passage alignments')
