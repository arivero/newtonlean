"""Extract source passages without silently merging TEI additions/deletions."""
from pathlib import Path
import hashlib
import json
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
NS = '{http://www.w3.org/XML/1998/namespace}'
SELECT = {'NATP00077': ['par25', 'par26', 'par27', 'par28'],
          'NATP00082': ['par26', 'par27', 'par28', 'par29', 'par30', 'par31', 'par32', 'par33', 'par34'],
          'NATP00089': ['par7', 'par9', 'par19'],
          'NATP00090': ['par12', 'par13', 'par27']}

def render(e):
    tag = e.tag.split('}')[-1]
    if tag == 'choice':
        return render(list(e)[0])  # diplomatic spelling, not orig+reg concatenation
    text = e.text or ''
    for c in e:
        text += render(c) + (c.tail or '')
    if tag in ('del', 'add', 'note', 'unclear'):
        text = f' [{tag}: {text}] '
    return text

def main():
    passages = []
    for ident, ids in SELECT.items():
        path = ROOT / 'docs/m1' / (ident + '.xml')
        tree = ET.parse(path)
        elements = {e.get(NS+'id'): e for e in tree.iter() if e.get(NS+'id')}
        title = ''.join(tree.find('.//{*}titleStmt/{*}title').itertext())
        companion = f'# {title}\n\nIsaac Newton; Newton Project {ident}. Retrieved 2026-09-21.\n\n'
        companion += f'Original: [{ident}.xml]({ident}.xml). Source: https://www.newtonproject.ox.ac.uk/view/texts/xml/{ident}\n\n'
        companion += 'Electronic transcription: CC BY-NC-ND 3.0 (TEI availability statement). '
        companion += 'XML parsed successfully; selected passages extracted, not a facsimile audit. '
        companion += 'Historical interpretation and formal discrepancies: ../../research/M1.md.\n\n'
        companion += 'SHA-256: `' + hashlib.sha256(path.read_bytes()).hexdigest() + '`\n'
        (path.with_suffix('.md')).write_text(companion)
        for view in ['normalized', 'diplomatic']:
            html = path.with_name(ident+'_'+view+'.html')
            if html.exists():
                html.with_suffix('.md').write_text(
                    f'# {title} — {view} view\n\n'
                    f'Isaac Newton; Newton Project {ident}. Retrieved 2026-09-21.\n\n'
                    f'Source: https://www.newtonproject.ox.ac.uk/view/texts/{view}/{ident}\n\n'
                    f'Local original: [{html.name}]({html.name}).\n\n'
                    'CC BY-NC-ND 3.0 per associated TEI. See the XML companion for '
                    'coverage and research/M1.md for proof obligations. Normalization '
                    'hides deletions; diplomatic markup and XML are required for revisions. '
                    'Page assets remain upstream; this is not an offline facsimile.\n\n'
                    f'SHA-256: `{hashlib.sha256(html.read_bytes()).hexdigest()}`\n')
        for pid in ids:
            e = elements[pid]
            passages.append({'id': ident+'.'+pid, 'witness': title,
                'url': f'https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/{ident}#{pid}',
                'latin': ' '.join(render(e).split())})
    dest = ROOT / 'research/passages.json'
    dest.write_text(json.dumps(passages, ensure_ascii=False, indent=2)+'\n')
    text = '# M1 primary passages\n\nMechanical TEI extraction: [del], [add], [note], [unclear] retain revision boundaries; spelling follows orig. Formula layout requires consultation of the original.\n\n'
    for p in passages:
        text += f'## {p["id"]}\n\nWitness: {p["witness"]}\n\n{p["url"]}\n\n{p["latin"]}\n\n'
    (ROOT/'research/passages.md').write_text(text)

if __name__ == '__main__':
    main()
