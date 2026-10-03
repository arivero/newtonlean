"""Render the dependency graphs as DOT sources and standalone images.

Pure standard library for the DOT and SVG output, so the script runs anywhere
`python3` does.  If Pillow happens to be importable, a PNG is written next to
each SVG; the PNG is a convenience preview, not the authority.

Layout is a plain layered (Sugiyama-style) drawing: rank by longest path from
the sources, then two barycentre passes to reduce crossings.  It is deliberately
small and deterministic rather than general.

These pictures visualise research/dependencies.json; check_graph.py is what
validates it (anchors, source identity, edge metadata, acyclicity).
"""
import json
from math import hypot
from pathlib import Path
from xml.sax.saxutils import escape

root = Path(__file__).resolve().parents[1]
data = json.loads((root / 'research/dependencies.json').read_text())
out_dir = root / 'docs/graphs'
out_dir.mkdir(parents=True, exist_ok=True)

# Names of graphs for which a PNG was written, in emission order; used to
# assemble the grouped PDF at the end.
EMITTED_PNG = []

nodes = {n['id']: n for n in data['nodes']}
edges = data['edges']

STAGE_COLOR = {
    'NATP00089': '#e8d5b7',
    'NATP00090': '#e8d5b7',
    '1687': '#cfe3f7',
    '1713': '#d6ecd2',
    '1726': '#f0d9ec',
    'proposed1694': '#f7e6c4',
    'RS-copy-reprint': '#e2e2e2',
}
RELATION_STYLE = {
    'proof_dependency': ('#33475b', 'solid'),
    'proposed_dependency': ('#8a6d1f', 'dashed'),
    'proposed_reordering': ('#8a6d1f', 'dotted'),
    'textual_comparison': ('#7a7a7a', 'dotted'),
}
STATUS_DASH = {'explicit_dependency': '', 'implicit_dependency': '6 4',
               'editorial_interpretation': '2 4', 'modern_reconstruction': '10 3 2 3'}
STATUS_LABELS = {'explicit_dependency': 'explicit dependency',
                 'implicit_dependency': 'implicit dependency',
                 'editorial_interpretation': 'editorial interpretation / comparison',
                 'modern_reconstruction': 'modern reconstruction'}

FONT = 12
CHAR_W = 6.4
PAD_X = 9
PAD_Y = 7
LINE_H = 15
COL_GAP = 74
ROW_GAP = 16
MARGIN = 26


def wrap(text, width):
    words, lines, cur = text.split(), [], ''
    for w in words:
        if cur and len(cur) + 1 + len(w) > width:
            lines.append(cur)
            cur = w
        else:
            cur = f'{cur} {w}'.strip()
    if cur:
        lines.append(cur)
    return lines or ['']


def formal_refs_of(node_id):
    """Formal references attached to any edge whose target is this node."""
    refs = []
    for e in edges:
        if e['to'] == node_id:
            refs.extend(e['formal_refs'])
    return sorted(set(refs))


class Node:
    def __init__(self, rec):
        self.id = rec['id']
        self.stage = rec['stage']
        self.type = rec['type']
        self.refs = formal_refs_of(self.id)
        lines = [self.id]
        lines += wrap(rec['statement'], 40)[:2]
        if self.refs:
            lines.append(f'{len(self.refs)} Lean result(s)')
        self.lines = lines
        self.w = max(len(l) for l in lines) * CHAR_W + 2 * PAD_X
        self.h = len(lines) * LINE_H + 2 * PAD_Y
        self.x = self.y = 0
        self.order = 0

    @property
    def cy(self):
        return self.y + self.h / 2

    @property
    def cx(self):
        return self.x + self.w / 2


def layout(node_ids, edge_list):
    node_ids = sorted(node_ids)
    ns = {i: Node(nodes[i]) for i in node_ids}
    adj = {i: [] for i in node_ids}
    radj = {i: [] for i in node_ids}
    for e in edge_list:
        if e['from'] in ns and e['to'] in ns:
            adj[e['from']].append(e['to'])
            radj[e['to']].append(e['from'])
    # longest-path ranking over the DAG (check_graph.py guarantees acyclicity)
    rank = {i: 0 for i in node_ids}
    indeg = {i: len(radj[i]) for i in node_ids}
    queue = sorted(i for i in node_ids if indeg[i] == 0)
    seen = set()
    while queue:
        u = queue.pop(0)
        if u in seen:
            continue
        seen.add(u)
        for v in adj[u]:
            rank[v] = max(rank[v], rank[u] + 1)
            indeg[v] -= 1
            if indeg[v] == 0:
                queue.append(v)
    for i in node_ids:  # anything left behind by a cycle keeps rank 0
        rank.setdefault(i, 0)
    columns = {}
    for i in node_ids:
        columns.setdefault(rank[i], []).append(i)
    for r in columns:
        columns[r].sort(key=lambda i: (nodes[i]['stage'], i))
    # two barycentre passes to reduce crossings
    for _ in range(2):
        for r in sorted(columns):
            if r == 0:
                continue
            prev = columns[r - 1]
            pos = {n: k for k, n in enumerate(prev)}
            def bary(i):
                ups = [pos[p] for p in radj[i] if p in pos]
                return sum(ups) / len(ups) if ups else float('inf')
            columns[r].sort(key=lambda i: (bary(i), nodes[i]['stage'], i))
    # coordinates
    x = MARGIN
    for r in sorted(columns):
        col_w = max(ns[i].w for i in columns[r])
        y = MARGIN + 44
        for i in columns[r]:
            n = ns[i]
            n.x = x + (col_w - n.w) / 2
            n.y = y
            y += n.h + ROW_GAP
        x += col_w + COL_GAP
    width = max(x - COL_GAP + MARGIN, 640)
    height = max(n.y + n.h for n in ns.values()) + MARGIN + 46
    return ns, [(e, ns[e['from']], ns[e['to']]) for e in edge_list
                if e['from'] in ns and e['to'] in ns], width, height


def legend_height(stages):
    return max(26 * len(stages) + 38, 164)


def edge_style(edge):
    return RELATION_STYLE[edge['relation']][0], STATUS_DASH[edge['status']]


def draw_polyline(draw, points, colour, dash='', width=1):
    """Draw dash lengths continuously through every corner of a PNG edge."""
    if not dash:
        draw.line(points, fill=colour, width=width, joint='curve')
        return
    pattern = tuple(float(length) for length in dash.split())
    index = 0
    remaining = pattern[0]
    for (x1, y1), (x2, y2) in zip(points, points[1:]):
        length = hypot(x2 - x1, y2 - y1)
        offset = 0.0
        while offset < length:
            step = min(remaining, length - offset)
            if index % 2 == 0:
                start = (x1 + (x2 - x1) * offset / length,
                         y1 + (y2 - y1) * offset / length)
                end = (x1 + (x2 - x1) * (offset + step) / length,
                       y1 + (y2 - y1) * (offset + step) / length)
                draw.line([start, end], fill=colour, width=width)
            offset += step
            remaining -= step
            if remaining < 1e-9:
                index = (index + 1) % len(pattern)
                remaining = pattern[index]


def to_svg(title, subtitle, ns, drawn, width, height):
    stages = sorted({n.stage for n in ns.values()})
    p = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width:.0f}" '
         f'height="{height + legend_height(stages):.0f}" viewBox="0 0 {width:.0f} '
         f'{height + legend_height(stages):.0f}" font-family="DejaVu Sans, Helvetica, sans-serif">',
         f'<rect width="100%" height="100%" fill="#ffffff"/>',
         f'<text x="{MARGIN}" y="26" font-size="16" font-weight="bold">{escape(title)}</text>',
         f'<text x="{MARGIN}" y="44" font-size="11" fill="#555">{escape(subtitle)}</text>',
         '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" '
         'markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
         '<path d="M 0 0 L 10 5 L 0 10 z" fill="context-stroke"/></marker></defs>']
    for e, a, b in drawn:
        colour, dash = edge_style(e)
        x1, y1 = a.x + a.w, a.cy
        x2, y2 = b.x, b.cy
        mx = (x1 + x2) / 2
        p.append(f'<path d="M {x1:.1f} {y1:.1f} C {mx:.1f} {y1:.1f}, {mx:.1f} {y2:.1f}, '
                 f'{x2:.1f} {y2:.1f}" fill="none" stroke="{colour}" stroke-width="1.3"'
                 + (f' stroke-dasharray="{dash}"' if dash else '')
                 + ' marker-end="url(#arrow)" opacity="0.85"/>')
    for n in ns.values():
        fill = STAGE_COLOR.get(n.stage, '#eeeeee')
        stroke = '#2c6e31' if n.refs else '#8d8d8d'
        sw = 2.2 if n.refs else 1.0
        p.append(f'<rect x="{n.x:.1f}" y="{n.y:.1f}" width="{n.w:.1f}" height="{n.h:.1f}" '
                 f'rx="5" fill="{fill}" stroke="{stroke}" stroke-width="{sw}"/>')
        for k, line in enumerate(n.lines):
            weight = ' font-weight="bold"' if k == 0 else ''
            colour = '#1a1a1a' if k == 0 else ('#2c6e31' if 'Lean result' in line else '#444')
            p.append(f'<text x="{n.x + PAD_X:.1f}" y="{n.y + PAD_Y + (k + 1) * LINE_H - 4:.1f}" '
                     f'font-size="{FONT}"{weight} fill="{colour}">{escape(line)}</text>')
    ly = height + 18
    p.append(f'<text x="{MARGIN}" y="{ly - 6}" font-size="12" font-weight="bold">Stages</text>')
    for k, s in enumerate(stages):
        p.append(f'<rect x="{MARGIN + 10}" y="{ly + k * 26}" width="16" height="14" '
                 f'fill="{STAGE_COLOR.get(s, "#eeeeee")}" stroke="#666"/>')
        count = sum(1 for n in ns.values() if n.stage == s)
        p.append(f'<text x="{MARGIN + 32}" y="{ly + k * 26 + 12}" font-size="11">'
                 f'{escape(s)} ({count} nodes)</text>')
    for k, (status, label) in enumerate(STATUS_LABELS.items()):
        y = ly + k * 26 + 7
        dash = STATUS_DASH[status]
        p.append(f'<path d="M {MARGIN + 240} {y} h 40" stroke="#33475b"'
                 + (f' stroke-dasharray="{dash}"' if dash else '') + '/>')
        p.append(f'<text x="{MARGIN + 290}" y="{y + 4}" font-size="11">{label}</text>')
    p.append(f'<text x="{MARGIN + 240}" y="{ly + 118}" font-size="11">'
             'green border = attached Lean references</text>')
    p.append(f'<text x="{MARGIN + 240}" y="{ly + 134}" font-size="11">'
             'references do not certify the historical claim</text>')
    p.append('</svg>')
    return '\n'.join(p)


def to_png(path, title, subtitle, ns, drawn, width, height):
    from PIL import Image, ImageDraw
    stages = sorted({n.stage for n in ns.values()})
    total_h = int(height + legend_height(stages))
    img = Image.new('RGB', (int(width), total_h), 'white')
    dr = ImageDraw.Draw(img)
    from PIL import ImageFont
    font = ImageFont.load_default()
    dr.text((MARGIN, 12), title, fill='black', font=font)
    dr.text((MARGIN, 32), subtitle, fill='#555555', font=font)
    for e, a, b in drawn:
        colour, dash = edge_style(e)
        draw_polyline(dr, [(a.x + a.w, a.cy), ((a.x + a.w + b.x) / 2, a.cy),
                          ((a.x + a.w + b.x) / 2, b.cy), (b.x, b.cy)], colour, dash)
        dr.polygon([(b.x, b.cy), (b.x - 7, b.cy - 4), (b.x - 7, b.cy + 4)], fill=colour)
    for n in ns.values():
        fill = STAGE_COLOR.get(n.stage, '#eeeeee')
        stroke = '#2c6e31' if n.refs else '#8d8d8d'
        dr.rounded_rectangle([n.x, n.y, n.x + n.w, n.y + n.h], radius=5,
                             fill=fill, outline=stroke, width=2 if n.refs else 1)
        for k, line in enumerate(n.lines):
            colour = '#1a1a1a' if k == 0 else ('#2c6e31' if 'Lean result' in line else '#444444')
            dr.text((n.x + PAD_X, n.y + PAD_Y + k * LINE_H - 2), line, fill=colour, font=font)
    ly = height + 18
    dr.text((MARGIN, ly - 16), 'Stages', fill='black', font=font)
    for k, stage in enumerate(stages):
        y = ly + k * 26
        dr.rectangle([MARGIN + 10, y, MARGIN + 26, y + 14],
                     fill=STAGE_COLOR.get(stage, '#eeeeee'), outline='#666666')
        count = sum(n.stage == stage for n in ns.values())
        dr.text((MARGIN + 32, y + 1), f'{stage} ({count} nodes)', fill='black', font=font)
    for k, (status, label) in enumerate(STATUS_LABELS.items()):
        y = ly + k * 26 + 7
        draw_polyline(dr, [(MARGIN + 240, y), (MARGIN + 280, y)],
                      '#33475b', STATUS_DASH[status])
        dr.text((MARGIN + 290, y - 6), label, fill='black', font=font)
    dr.text((MARGIN + 240, ly + 108), 'green border = attached Lean references',
            fill='black', font=font)
    dr.text((MARGIN + 240, ly + 124), 'references do not certify the historical claim',
            fill='black', font=font)
    img.save(path)


def to_dot(name, ns, drawn):
    p = [f'digraph {name} {{', '  rankdir=LR;', '  node [shape=box, style="rounded,filled"];']
    for n in ns.values():
        label = '\\n'.join(n.lines).replace('"', "'")
        colour = STAGE_COLOR.get(n.stage, '#eeeeee')
        border = '#2c6e31' if n.refs else '#8d8d8d'
        p.append(f'  "{n.id}" [label="{label}", fillcolor="{colour}", color="{border}", '
                 f'penwidth={2 if n.refs else 1}];')
    for e, a, b in drawn:
        style = {'explicit_dependency': 'solid', 'implicit_dependency': 'dashed',
                 'editorial_interpretation': 'dotted',
                 'modern_reconstruction': 'dashed'}[e['status']]
        p.append(f'  "{e["from"]}" -> "{e["to"]}" [style={style}, '
                 f'label="{e["relation"].replace("_", " ")}: {e["status"]}", fontsize=9];')
    p.append('}')
    return '\n'.join(p)


def emit(name, title, subtitle, node_ids, edge_list):
    ns, drawn, width, height = layout(list(node_ids), edge_list)
    (out_dir / f'{name}.svg').write_text(to_svg(title, subtitle, ns, drawn, width, height))
    (out_dir / f'{name}.dot').write_text(to_dot(name, ns, drawn))
    try:
        to_png(out_dir / f'{name}.png', title, subtitle, ns, drawn, width, height)
        png = 'png+svg+dot'
        EMITTED_PNG.append(name)
    except ImportError:
        png = 'svg+dot'
    print(f'{name}: {len(ns)} nodes, {len(drawn)} edges -> {png}')
    return len(ns), len(drawn)


def build_pdf(names):
    """Group every emitted PNG into one multi-page PDF, one graph per page."""
    if not names:
        return None
    try:
        from PIL import Image
    except ImportError:
        print('all-graphs.pdf: skipped (Pillow not available)')
        return None
    imgs = [Image.open(out_dir / f'{n}.png').convert('RGB') for n in names]
    pdf = out_dir / 'all-graphs.pdf'
    imgs[0].save(pdf, save_all=True, append_images=imgs[1:], resolution=100.0)
    for im in imgs:
        im.close()
    print(f'all-graphs.pdf: {len(imgs)} pages -> {pdf.name}')
    return pdf


proof = [e for e in edges if e['relation'] == 'proof_dependency']
proposed = [e for e in edges if e['relation'] in ('proposed_dependency', 'proposed_reordering')]
comparison = [e for e in edges if e['relation'] == 'textual_comparison']

totals = []
for stage, label in (('1687', '1687 Principia, Book I'), ('1713', '1713 Principia, Book I')):
    ids = {n['id'] for n in data['nodes'] if n['stage'] == stage}
    sub = [e for e in proof if e['from'] in ids and e['to'] in ids]
    used = {e['from'] for e in sub} | {e['to'] for e in sub}
    totals.append(emit(f'proof-{stage}', f'Proof dependencies - {label}',
                       'arrow: cited result -> result that cites it; green = attached Lean references',
                       used or ids, sub))
ids1726 = {n['id'] for n in data['nodes'] if n['stage'] == '1726'}
sub = [e for e in proof if e['from'] in ids1726 and e['to'] in ids1726]
used = {e['from'] for e in sub} | {e['to'] for e in sub}
totals.append(emit('proof-1726', 'Proof dependencies - 1726 Principia',
                   'comparison witness; 1726 edges never supply earlier premises',
                   used or ids1726, sub))
draft_ids = {n['id'] for n in data['nodes']
             if n['stage'] in ('NATP00089', 'NATP00090', 'RS-copy-reprint', 'proposed1694')}
sub = [e for e in proof + proposed if e['from'] in draft_ids and e['to'] in draft_ids]
used = {e['from'] for e in sub} | {e['to'] for e in sub}
totals.append(emit('proof-drafts', 'De Motu, drafts and the proposed 1694 ordering',
                   'edge pattern gives evidence status; ochre arrows are proposed-stage edges',
                   used or draft_ids, sub))
comp_ids = {e['from'] for e in comparison + proposed} | {e['to'] for e in comparison + proposed}
totals.append(emit('comparison', 'Textual comparison and proposed reordering',
                   'cross-stage comparison edges only; these are not proof dependencies',
                   comp_ids, comparison + proposed))
sectionII = set()
for tag in ('P1', 'P2', 'P3', 'P4'):
    for pref in ('P1687.', 'P1713.'):
        if pref + tag in nodes:
            sectionII.add(pref + tag)
frontier = set(sectionII)
sub_edges = []
for _ in range(6):
    nxt = set()
    for e in proof:
        if e['to'] in frontier:
            sub_edges.append(e)
            nxt.add(e['from'])
    frontier = nxt - sectionII
    if not frontier:
        break
    sectionII |= frontier
totals.append(emit('section-II', 'Section II, Propositions I-IV and everything they cite',
                   'both editions in one picture; transitive closure of the cited dependencies',
                   sectionII, sub_edges))
totals.append(emit('formalisation-coverage', 'Formalisation coverage of the whole evidence graph',
                   'every node, ranked by dependency depth; green = attached Lean references',
                   set(nodes), proof + proposed))

build_pdf(EMITTED_PNG)

print('totals:', sum(t[0] for t in totals), 'node placements,',
      sum(t[1] for t in totals), 'edges drawn')
