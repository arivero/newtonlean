"""Interleave the modern Principia rendering with the Lean theorems anchored to it.

Reads docs/reference/principia-1687-modern.md, research/formal-results.json
and the Lean sources at a git revision (default HEAD), and writes
docs/reference/principia-with-lean.md: after each Definition, Law, Lemma,
Proposition or Scholium, the theorems whose catalogued source passages cite
that item appear in a smaller monospace face, statement and proof, grouped by
module in import order and preceded by the module's docstring.  Theorems with
no source passage (the foundation) are listed by statement only in an
appendix, as are theorems anchored outside the rendered range.

Build the PDF with

    pandoc docs/reference/principia-with-lean.md -o docs/reference/principia-with-lean.pdf \
      --pdf-engine=xelatex -V mainfont="DejaVu Serif" -V monofont="DejaVu Sans Mono" \
      -V mathfont="DejaVu Math TeX Gyre" --toc --toc-depth=2
"""
import json
import re
import subprocess
import sys
from collections import OrderedDict, defaultdict
from pathlib import Path

root = Path(__file__).resolve().parents[1]
REV = sys.argv[1] if len(sys.argv) > 1 else 'HEAD'
SRC = root / 'docs/reference/principia-1687-modern.md'
OUT = root / 'docs/reference/principia-with-lean.md'


def git(*args):
    return subprocess.run(['git', '-C', str(root), *args], capture_output=True,
                          text=True, check=True).stdout


# ---------------------------------------------------------------- items
# Heading as it appears in the rendering, and the paragraph anchors of that
# item in 1687 (NATP00075/76/77), 1713 (NATP00080/81/82), 1726 (85/86/87)
# and De Motu (NATP00089/90).  Only anchors that the catalogue can cite
# matter; Scholia are items of their own.

def rng(doc, a, b):
    return [f'{doc}.par{i}' for i in range(a, b + 1)]


ITEMS = [
    ('**Definition I.**', rng('NATP00075', 1, 2) + rng('NATP00080', 1, 2) + rng('NATP00085', 1, 2)),
    ('**Definition II.**', rng('NATP00075', 3, 4) + rng('NATP00080', 3, 4) + rng('NATP00085', 3, 4)),
    ('**Definition III.**', rng('NATP00075', 5, 6) + rng('NATP00080', 5, 6) + rng('NATP00085', 5, 6)),
    ('**Definition IV.**', rng('NATP00075', 7, 8) + rng('NATP00080', 7, 8) + rng('NATP00085', 7, 8)),
    ('**Definition V.**', rng('NATP00075', 9, 10) + rng('NATP00080', 9, 10) + rng('NATP00085', 9, 10)),
    ('**Definition VI.**', rng('NATP00075', 11, 12) + rng('NATP00080', 11, 12) + rng('NATP00085', 11, 12)),
    ('**Definition VII.**', rng('NATP00075', 13, 14) + rng('NATP00080', 13, 14) + rng('NATP00085', 13, 14)),
    ('**Definition VIII.**', rng('NATP00075', 15, 19) + rng('NATP00080', 15, 19) + rng('NATP00085', 15, 19)),
    ('## Scholium', rng('NATP00075', 20, 34) + rng('NATP00080', 20, 36) + rng('NATP00085', 20, 37)),
    ('**Law I.**', rng('NATP00076', 1, 2) + rng('NATP00081', 1, 2) + rng('NATP00086', 1, 2) + ['NATP00090.par5']),
    ('**Law II.**', rng('NATP00076', 3, 4) + rng('NATP00081', 3, 4) + rng('NATP00086', 3, 4)),
    ('**Law III.**', rng('NATP00076', 5, 6) + rng('NATP00081', 5, 6) + rng('NATP00086', 5, 6)),
    ('**Corollary I.**', rng('NATP00076', 7, 8) + rng('NATP00081', 7, 8) + rng('NATP00086', 7, 8)),
    ('**Corollary II.**', rng('NATP00076', 9, 12) + rng('NATP00081', 9, 12) + rng('NATP00086', 9, 12)),
    ('**Corollary III.**', rng('NATP00076', 13, 16) + rng('NATP00081', 13, 16) + rng('NATP00086', 13, 16)),
    ('**Corollary IV.**', rng('NATP00076', 17, 19) + rng('NATP00081', 17, 19) + rng('NATP00086', 17, 19)),
    ('**Corollary V.**', rng('NATP00076', 20, 21) + rng('NATP00081', 20, 21) + rng('NATP00086', 20, 21)),
    ('**Corollary VI.**', rng('NATP00076', 22, 23) + rng('NATP00081', 22, 23) + rng('NATP00086', 22, 23)),
    ('## Scholium', rng('NATP00076', 24, 28) + rng('NATP00081', 24, 29) + rng('NATP00086', 24, 30)),
    ('**Lemma I.**', rng('NATP00077', 1, 2) + rng('NATP00082', 2, 3)),
    ('**Lemma II.**', rng('NATP00077', 3, 4) + rng('NATP00082', 4, 5)),
    ('**Lemma III.**', rng('NATP00077', 5, 10) + rng('NATP00082', 6, 11)),
    ('**Lemma IV.**', rng('NATP00077', 11, 13) + rng('NATP00082', 12, 14)),
    ('**Lemma V.**', ['NATP00077.par14', 'NATP00082.par15']),
    ('**Lemma VI.**', rng('NATP00077', 15, 16) + rng('NATP00082', 16, 17)),
    ('**Lemma VII.**', rng('NATP00077', 17, 21) + rng('NATP00082', 18, 22)),
    ('**Lemma VIII.**', rng('NATP00077', 22, 24) + rng('NATP00082', 23, 25)),
    ('**Lemma IX.**', rng('NATP00077', 25, 26) + rng('NATP00082', 26, 27)),
    ('**Lemma X.**', rng('NATP00077', 27, 30) + rng('NATP00082', 28, 35)),
    ('**Lemma XI.**', rng('NATP00077', 31, 37) + rng('NATP00082', 36, 44)),
    ('### Scholium', rng('NATP00077', 38, 42) + rng('NATP00082', 45, 48)),
    ('**Proposition I. Theorem I.**', rng('NATP00077', 44, 47) + rng('NATP00082', 50, 57)
     + rng('NATP00089', 8, 9) + rng('NATP00090', 16, 17)),
    ('**Proposition II. Theorem II.**', rng('NATP00077', 48, 50) + rng('NATP00082', 58, 62)),
    ('### Scholium', rng('NATP00077', 51, 52) + ['NATP00082.par63']),
    ('**Proposition III. Theorem III.**', rng('NATP00077', 53, 58) + rng('NATP00082', 64, 69)),
    ('### Scholium', ['NATP00077.par59', 'NATP00082.par70']),
    ('**Proposition IV. Theorem IV.**', rng('NATP00077', 60, 68) + rng('NATP00082', 71, 81)
     + rng('NATP00089', 10, 11) + rng('NATP00090', 18, 19)),
    ('### Scholium', rng('NATP00077', 69, 72) + rng('NATP00082', 82, 84)),
]
ANCHOR_TO_ITEM = {}
for idx, (_, anchors) in enumerate(ITEMS):
    for a in anchors:
        ANCHOR_TO_ITEM.setdefault(a, idx)

# ------------------------------------------------------------- Lean sources

DECL_LINE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+(\S+)')
NS_LINE = re.compile(r'^namespace\s+(\S+)')
END_LINE = re.compile(r'^end(?:\s+(\S+))?\s*$')


def source_blocks(text):
    """Map local theorem name -> (qualified name, raw block including docstring)."""
    lines = text.split('\n')
    ns = []
    out = {}
    i = 0
    while i < len(lines):
        line = lines[i]
        m = NS_LINE.match(line)
        if m:
            ns.extend(m.group(1).split('.'))
        elif END_LINE.match(line) and not line.startswith('end '):
            pass
        elif line.startswith('end ') and ns:
            name = line.split()[1]
            for _ in name.split('.'):
                if ns:
                    ns.pop()
        m = DECL_LINE.match(line)
        if m:
            start = i
            # include a docstring immediately above
            j = i - 1
            while j >= 0 and lines[j].strip() == '':
                j -= 1
            if j >= 0 and lines[j].rstrip().endswith('-/'):
                k = j
                while k >= 0 and not lines[k].lstrip().startswith('/--'):
                    k -= 1
                if k >= 0:
                    start = k
            e = i + 1
            while e < len(lines) and (lines[e] == '' or lines[e][0].isspace()):
                e += 1
            while e > i + 1 and lines[e - 1] == '':
                e -= 1
            local = m.group(1)
            qual = '.'.join(ns + [local])
            out[qual] = '\n'.join(lines[start:e])
            i = e
            continue
        i += 1
    return out


def docstring(text):
    m = re.search(r'/-!(.*?)-/', text, re.S)
    return ' '.join(m.group(1).split()) if m else ''


def module_order():
    order = []
    for lib in ('BarrowLib.lean', 'NewtonLimitDynamics.lean'):
        for line in git('show', f'{REV}:{lib}').split('\n'):
            if line.startswith('import '):
                order.append(line[7:].strip().replace('.', '/') + '.lean')
    return {f: i for i, f in enumerate(order)}


# -------------------------------------------------------------------- main

def main():
    catalogue = json.loads(git('show', f'{REV}:research/formal-results.json'))
    order = module_order()
    files = sorted({r['file'] for r in catalogue}, key=lambda f: order.get(f, 10_000))
    sources, docs = {}, {}
    for f in files:
        try:
            text = git('show', f'{REV}:{f}')
        except subprocess.CalledProcessError:
            continue
        sources[f] = source_blocks(text)
        docs[f] = docstring(text)

    per_item = defaultdict(lambda: OrderedDict())   # item idx -> file -> [entries]
    outside = OrderedDict()
    foundation = OrderedDict()
    for r in catalogue:
        target = None
        for a in r['source_passages']:
            if a in ANCHOR_TO_ITEM:
                target = ANCHOR_TO_ITEM[a]
                break
        if r['source_passages'] and target is None:
            outside.setdefault(r['file'], []).append(r)
        elif target is None:
            foundation.setdefault(r['file'], []).append(r)
        else:
            per_item[target].setdefault(r['file'], []).append(r)

    def verbatim(text, size='scriptsize'):
        return f'\\begin{{Verbatim}}[breaklines,breakanywhere,fontsize=\\{size}]\n{text}\n\\end{{Verbatim}}\n'

    def block_for(r, with_proof):
        local = r['name'].split('.')[-1]
        if with_proof:
            src = sources.get(r['file'], {})
            body = src.get(r['name']) or next((v for k, v in src.items() if k.endswith('.' + local)), None)
            if body:
                return body
        head = 'private theorem' if r['private'] else 'theorem'
        return f"{head} {local} {r['premise_signature']}"

    def render_group(groups, with_proof, size='scriptsize'):
        parts = []
        for f, entries in groups.items():
            doc = docs.get(f, '')
            if len(doc) > 600:
                doc = doc[:600].rsplit(' ', 1)[0] + ' …'
            parts.append(f'\\noindent{{\\small\\texttt{{{f}}}}}{" — " + doc if doc else ""}\n')
            parts.append(verbatim('\n\n'.join(block_for(r, with_proof) for r in entries), size))
        return '\n'.join(parts)

    def item_block(idx):
        groups = per_item.get(idx)
        if not groups:
            return ('\\noindent{\\small\\textit{No theorem of the Lean reconstruction cites this item.}}\n')
        n = sum(len(v) for v in groups.values())
        head = (f'\\noindent{{\\small\\textit{{Lean reconstruction: {n} theorem{"s" if n != 1 else ""} '
                f'in {len(groups)} module{"s" if len(groups) != 1 else ""} cite this item; statements and proofs follow, '
                f'by module in import order.}}}}\n')
        return head + '\n' + render_group(groups, with_proof=True)

    # ---- walk the rendering and insert after each item
    lines = SRC.read_text().split('\n')
    out = []
    item_idx = -1          # index into ITEMS of the item currently open
    expected = 0           # next ITEMS entry to match
    HEAD = re.compile(r'^(#{1,3} |\*\*(Definition|Law|Corollary|Lemma|Proposition)[^*]*\*\*)')
    in_yaml = False
    for i, line in enumerate(lines):
        if i == 0 and line.strip() == '---':
            in_yaml = True
        if in_yaml:
            if line.startswith('title:'):
                line = 'title: "Newton, *Principia*, with its Lean reconstruction interleaved"'
            elif line.startswith('subtitle:'):
                line = ('subtitle: "The 1687 Definitions, Laws and Book I Sections I–II in modern language, '
                        'each item followed by the theorems that formalize it"')
            elif line.startswith('header-includes:') or line.startswith('  - \\usepackage'):
                pass
            if line.strip() == '---' and i > 0:
                out.append('header-includes:')
                out.append('  - \\usepackage{fvextra}')
                out.append('  - \\usepackage{amsmath}')
                out.append('  - \\usepackage{amssymb}')
                out.append('  - \\fvset{fontfamily=tt}')
                out.append(line)
                in_yaml = False
                continue
            out.append(line)
            continue
        if HEAD.match(line):
            # close the open item: emit its Lean block before this heading
            if item_idx >= 0:
                out.append('')
                out.append(item_block(item_idx))
                out.append('')
                item_idx = -1
            if expected < len(ITEMS) and line.startswith(ITEMS[expected][0]):
                item_idx = expected
                expected += 1
        out.append(line)
    if item_idx >= 0:
        out.append('')
        out.append(item_block(item_idx))
    if expected != len(ITEMS):
        print(f'warning: matched {expected} of {len(ITEMS)} items', file=sys.stderr)

    # ---- how to read, inserted after the first heading paragraph
    intro = """
## How to read this version

After each Definition, Law, Lemma, Proposition or Scholium, the theorems of
the Lean reconstruction whose catalogued source passages cite that item are
printed in a smaller monospace face, with their docstrings, statements and
proofs, grouped by module in import order. The catalogue
(`research/formal-results.json`) assigns each theorem to Newton Project
paragraph anchors; a theorem citing several items is printed under the first.
Items that no theorem cites say so. The Lean is a modern reconstruction in
rational arithmetic with Lean 4 core only: it supplies no historical premise,
and its appearance under an item records that the item motivated it, not that
the item is thereby proved. Two appendices list, by statement only, the
theorems anchored outside the rendered range and the foundation theorems
with no source anchor, which are most of the code.
"""
    text = '\n'.join(out)
    text = text.replace('\n## How the editions differ', intro + '\n## How the editions differ', 1)

    # ---- appendices
    n_out = sum(len(v) for v in outside.values())
    n_found = sum(len(v) for v in foundation.values())
    text += '\n\n# Appendix A. Theorems anchored outside Sections I–II\n\n'
    text += (f'{n_out} theorems cite passages outside the rendered range (Proposition VI and its '
             'later-edition counterparts, the Section I Scholium on vanishing quantities as cited '
             'for Lemma X, and the De Motu comparison chain). Statements only.\n\n')
    text += render_group(outside, with_proof=False)
    text += '\n\n# Appendix B. The foundation: theorems with no source anchor\n\n'
    text += (f'{n_found} theorems have no Newton anchor. They build the rational arithmetic, '
             'point algebra, finite estimates, Cauchy names and quotient values, binary time, '
             'square covers and the generic lifting of operations to completed values on which '
             'the anchored proofs stand. Statements only, by module in import order.\n\n')
    text += render_group(foundation, with_proof=False)
    OUT.write_text(text.rstrip('\n') + '\n')
    n_items = sum(len(v) for g in per_item.values() for v in g.values())
    print(f'{OUT.relative_to(root)}: {n_items} anchored theorems under {len(per_item)} items, '
          f'{n_out} outside, {n_found} foundation; {len(text):,} chars')


if __name__ == '__main__':
    main()
