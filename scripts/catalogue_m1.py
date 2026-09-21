"""Extract source passages without silently merging TEI additions/deletions."""
from pathlib import Path
import hashlib
import json
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
NS = '{http://www.w3.org/XML/1998/namespace}'
SELECT = json.loads((ROOT/'research/selections.json').read_text())
ANNOTATIONS = json.loads((ROOT/'research/passage-annotations.json').read_text())

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
    for ident, selection in SELECT.items():
        ids = selection['anchors']
        path = ROOT / selection['path']
        tree = ET.parse(path)
        elements = {e.get(NS+'id'): e for e in tree.iter() if e.get(NS+'id')}
        title = ''.join(tree.find('.//{*}titleStmt/{*}title').itertext())
        companion = f'# {title}\n\nIsaac Newton; Newton Project {ident}. Retrieved 2026-09-21.\n\n'
        companion += f'Original: [{ident}.xml]({ident}.xml). Source: https://www.newtonproject.ox.ac.uk/view/texts/xml/{ident}\n\n'
        companion += 'Electronic transcription: CC BY-NC-ND 3.0 (TEI availability statement). '
        companion += 'XML parsed successfully; selected passages extracted, not a facsimile audit. '
        companion += 'Historical interpretation and formal discrepancies: ../../research/STATE.md and milestone reports.\n\n'
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
                    'coverage and research/STATE.md for proof obligations. Normalization '
                    'hides deletions; diplomatic markup and XML are required for revisions. '
                    'Page assets remain upstream; this is not an offline facsimile.\n\n'
                    f'SHA-256: `{hashlib.sha256(html.read_bytes()).hexdigest()}`\n')
        for pid in ids:
            e = elements[pid]
            passages.append({'id': ident+'.'+pid, 'witness': title,
                'stage': selection['stage'], 'source_path': selection['path'],
                'anchor': pid, 'revision_layer': selection['revision_layer'],
                'translation': ANNOTATIONS.get(ident+'.'+pid, {}).get('translation'),
                'translation_status': 'identifying_translation_not_full' if ident+'.'+pid in ANNOTATIONS else 'not_translated',
                'formal_refs': ANNOTATIONS.get(ident+'.'+pid, {}).get('formal_refs', []),
                'tei': ET.tostring(e, encoding='unicode'),
                'url': f'https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/{ident}#{pid}',
                'latin': ' '.join(render(e).split())})
    passages.extend(json.loads((ROOT/'research/extra-passages.json').read_text()))
    dest = ROOT / 'research/passages.json'
    dest.write_text(json.dumps(passages, ensure_ascii=False, indent=2)+'\n')
    text = '# Primary passages: separate witnesses\n\nMechanical TEI extraction: [del], [add], [note], [unclear] retain revision boundaries; spelling follows orig. Formula layout requires consultation of the original.\n\n'
    for p in passages:
        text += f'## {p["id"]}\n\nWitness: {p["witness"]}\n\n{p["url"]}\n\n{p.get("text", p["latin"])}\n\nTranslation status: {p.get("translation_status", "not_translated")}. {p.get("translation") or ""}\n\n'
    (ROOT/'research/passages.md').write_text('\n'.join(line.rstrip() for line in text.splitlines())+'\n')

if __name__ == '__main__':
    main()
