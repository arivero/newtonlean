"""Interleave the modern Principia rendering with the Lean theorems anchored to it.

Reads docs/reference/principia-1687-modern.md, research/formal-results.json
and the Lean sources at a git revision (default HEAD), and writes
docs/reference/principia-with-lean.md: after each Definition, Law, Lemma,
Proposition or Scholium, every module whose theorems cite that item is
printed in full, verbatim, in a smaller monospace face (definitions,
docstrings, statements and proofs), in import order.  A module whose theorems
cite several items is printed under the item most of them cite, with a
cross-reference under the others.  Modules with no source anchor (the
foundation) and modules anchored outside the rendered range are printed in
full in two appendices.  Every line of the two libraries appears exactly once.

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
# Where each item lives in the Lean when no theorem cites it, or in addition
# to the theorems that do.  Editorial; verified against the sources at HEAD.
NOTES = {
    0: "Not encoded. The model has no mass: forces are accelerative (Definition VII). A `mass` parameter appears only in the potential and circular diagnostics (`Diagnostic/ConstructedHarmonicPotential`, `Comparison/CircleCompare`).",
    1: "Not encoded; with mass absent, velocity stands in for quantity of motion.",
    2: "Encoded, not proved: the inertial drift `pointAdd s.1 (pointScale d s.2)` that opens every cell (`CentralSchedule.cell`), and `ZeroForce.inertialAt`.",
    3: "Encoded, not proved: the velocity kick `pointAdd s.2 (pointScale d (a y))` at the arrival vertex of every cell (`CentralSchedule.cell`, `TimeSubdivision.endKick`).",
    4: "Encoded as the predicate `CentralSchedule.central` (`det p (a p) = 0`: the force is parallel to the radius) and the `inward` field of `ForceClasses.CentralOracle` (every sample a nonnegative multiple of `-p`).",
    5: "Not encoded.",
    6: "Encoded: a force is a map `Field := Point → Point` from positions to accelerations (`CentralSchedule`), or its rational samples with error (`ForceClasses.Oracle`).",
    7: "Not encoded (no mass).",
    8: "Absolute time is the rational parameter of every schedule and, in the completed layer, the constructed `BinaryTime` quotient; absolute space is the rational plane `Point := Fraction × Fraction` (`TimeSubdivision`). Relative motion appears only as the uniformly moving centre of Proposition II, Case 2.",
    9: "Also encoded as the drift in every cell, and stated as `RelativeMotion.lawI_uniform` (printed under Proposition III, which cites it).",
    10: "Encoded in impulse form by the kick of `CentralSchedule.cell`: the change of velocity is `d · a(y)`, along the force and proportional to it; and by `Finite.EuclideanConstruction.kick`, which displaces the vertex parallel to the radius.",
    11: "Not encoded: the model is single-body. Proposition III cancels the second body's force by Corollary VI, not by Law III.",
    12: "Encoded as `Finite.step g p q j = g.kick q (g.extend p q) j` with the field `same_base_parallels` of `EuclideanConstruction`: the displaced vertex lies on the line through the inertial point parallel to the radius, Newton's parallelogram.",
    13: "Not encoded.",
    14: "Not encoded (no mass, single body).",
    15: "Not encoded.",
    16: "Used as `Converse.moving_centre_equal_areas_central`, Proposition II, Case 2 (printed under Proposition II).",
    17: "Stated and used as `RelativeMotion.corVI_relative` (printed under Proposition III, whose dependency edge in `research/dependencies.json` names it).",
    18: "Not encoded, except that Galileo's parabola is the parallel-force instance `ForceClasses.parallelOracle` and `Polygon/ParallelQuadraticEndpoint`.",
    19: "Encoded as the limit interface of `BarrowLib/Common/Quadratic.lean`: `Near` and `Ultimate` (ultimate equality is approach closer than any given difference), used by `enclosure_reconstruction`, the squeeze; and as the `Within` and `Vanishes` predicates of `CauchyValues` and `Enclosure`.",
    20: "Not separately encoded; its equal-base step sums appear with Lemma III.",
    21: "Corollary 4, the passage Proposition I cites for its limit, is the premise named `PolygonTrajectoryEnclosure` in `Polygon/PathDefect.lean`: assumed by the edition theorems, not derived.",
    22: "Not encoded.",
    23: "Not encoded; Proposition IV's limiting route through it is documented as an editorial interpretation, not derived.",
    24: "Not encoded; the chord, tangent and arc comparison is not needed by the finite steps of Propositions I–IV.",
    25: "Not encoded (see Lemma VI).",
    26: "Not encoded (see Lemma VI).",
    30: "Not encoded; its distinction between vanishing divisible quantities and indivisibles is the reading the rational construction follows.",
    33: "Not encoded.",
    35: "Not encoded.",
    37: "Not encoded; the polygon-reflection argument has no counterpart.",
}

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
    # every library file at the revision, not only those with catalogued theorems
    files = sorted((f for f in git('ls-tree', '-r', '--name-only', REV).split('\n')
                    if f.endswith('.lean') and f.startswith(('NewtonLimitDynamics/', 'BarrowLib/'))),
                   key=lambda f: order.get(f, 10_000))
    # file-level source correspondence from the catalogue script, for files
    # that define things but prove no theorem
    import ast
    file_anchors = {}
    try:
        tree = ast.parse(git('show', f'{REV}:scripts/catalogue_formal.py'))
        for node in tree.body:
            if isinstance(node, ast.Assign) and node.targets[0].id == 'correspondence':
                for rel, (srcs, _note) in ast.literal_eval(node.value).items():
                    file_anchors[rel] = srcs
    except Exception as e:  # noqa: BLE001
        print('warning: no file-level correspondence:', e, file=sys.stderr)
    sources, docs = {}, {}
    for f in files:
        try:
            text = git('show', f'{REV}:{f}')
        except subprocess.CalledProcessError:
            continue
        sources[f] = source_blocks(text)
        docs[f] = docstring(text)

    texts = {}
    for f in files:
        try:
            texts[f] = git('show', f'{REV}:{f}')
        except subprocess.CalledProcessError:
            pass
    # item votes per file: which items its theorems cite
    votes = defaultdict(lambda: defaultdict(int))
    outside_files, foundation_files = [], []
    for r in catalogue:
        target = None
        for a in r['source_passages']:
            if a in ANCHOR_TO_ITEM:
                target = ANCHOR_TO_ITEM[a]
                break
        if target is not None:
            votes[r['file']][target] += 1
        elif r['source_passages']:
            votes[r['file']][-1] += 1       # outside the rendered range
        else:
            votes[r['file']][-2] += 1       # foundation
    home = {}                               # file -> item index, -1 outside, -2 foundation
    for f in files:
        if f not in texts:
            continue
        v = votes.get(f)
        if not v:
            rel = f.split('/', 1)[1] if '/' in f else f
            anchors = file_anchors.get(rel, [])
            hit = next((ANCHOR_TO_ITEM[a] for a in anchors if a in ANCHOR_TO_ITEM), None)
            home[f] = hit if hit is not None else (-1 if anchors else -2)
        else:
            home[f] = max(v.items(), key=lambda kv: (kv[1], -kv[0]))[0]
    per_item = defaultdict(list)
    for f in files:
        if f in home:
            per_item[home[f]].append(f)
    # also the two root import files, so that every library line appears
    roots = []
    for lib in ('BarrowLib.lean', 'NewtonLimitDynamics.lean'):
        try:
            texts[lib] = git('show', f'{REV}:{lib}')
            roots.append(lib)
        except subprocess.CalledProcessError:
            pass

    def verbatim(text, size='scriptsize'):
        return f'\\begin{{Verbatim}}[breaklines,breakanywhere,fontsize=\\{size}]\n{text.rstrip()}\n\\end{{Verbatim}}\n'

    def render_files(fs, size='scriptsize'):
        parts = []
        for f in fs:
            n = sum(votes[f].values()) if f in votes else 0
            what = f'{n} theorem{"s" if n != 1 else ""}' if n else 'definitions only'
            parts.append(f'\\noindent{{\\small\\texttt{{{f}}}}}{{\\small, {what}, '
                         f'{texts[f].count(chr(10))} lines}}\n')
            parts.append(verbatim(texts[f], size))
        return '\n'.join(parts)

    def item_block(idx):
        fs = per_item.get(idx, [])
        others = [(f, votes[f][idx]) for f in files if f in home and home[f] != idx and votes.get(f, {}).get(idx)]
        note = NOTES.get(idx)
        if not fs and not others:
            txt = 'No theorem of the Lean reconstruction cites this item.'
            if note:
                txt += ' ' + note
            return '\\noindent{\\small\\textit{' + txt.replace('_', '\\_') + '}}\n'
        n = sum(votes[f][idx] for f in fs)
        head = (f'\\noindent{{\\small\\textit{{Lean reconstruction: {n} theorem{"s" if n != 1 else ""} '
                f'in {len(fs)} module{"s" if len(fs) != 1 else ""} cite this item; the modules follow in full, '
                f'in import order.}}}}\n')
        if others:
            names = [f'{ITEMS[home[f]][0].strip("*#").strip()} ({f.split("/")[-1]}, {c})' for f, c in others]
            head += ('\n\\noindent{\\small\\textit{Also cited by theorems printed under: ' + '; '.join(names) + '.}}\n')
        if note:
            head += '\n\\noindent{\\small\\textit{' + note.replace('_', '\\_') + '}}\n'
        return head + '\n' + render_files(fs)

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
printed as complete modules in a smaller monospace face: definitions,
docstrings, statements and proofs, verbatim, in import order. The catalogue
(`research/formal-results.json`) assigns each theorem to Newton Project
paragraph anchors; a module whose theorems cite several items is printed
under the item most of them cite, with a cross-reference under the others.
Items that no theorem cites say so. The Lean is a modern reconstruction in
rational arithmetic with Lean 4 core only: it supplies no historical premise,
and its appearance under an item records that the item motivated it, not that
the item is thereby proved. Two appendices print, in full, the modules
anchored outside the rendered range and the foundation modules with no source
anchor, which are most of the code. Every line of the two libraries appears
exactly once; the verification harnesses under `research/verification` are
not included.
"""
    text = '\n'.join(out)
    text = text.replace('\n## How the editions differ', intro + '\n## How the editions differ', 1)

    # ---- appendices
    out_files = per_item.get(-1, [])
    found_files = per_item.get(-2, [])
    n_out = sum(sum(votes[f].values()) for f in out_files)
    n_found = sum(len([r for r in catalogue if r['file'] == f]) for f in found_files)
    text += '\n\n# Appendix A. Modules anchored outside Sections I–II\n\n'
    text += (f'{len(out_files)} module{"s" if len(out_files) != 1 else ""} with {n_out} theorems are anchored to passages '
             'outside the rendered range: Proposition VI and its later-edition counterparts, and the De Motu '
             'quadratic-deflection chain of the M1 milestone.\n\n')
    text += render_files(out_files)
    text += '\n\n# Appendix B. The foundation: modules with no source anchor\n\n'
    text += (f'{len(found_files)} modules with {n_found} theorems have no Newton anchor. They build the rational '
             'arithmetic, point algebra, finite estimates, Cauchy names and quotient values, binary time, '
             'square covers and the lifting of operations to completed values on which the anchored proofs '
             'stand. In full, in import order, followed by the two library root files.\n\n')
    text += render_files(found_files + roots)
    OUT.write_text(text.rstrip('\n') + '\n')
    n_items = sum(len(v) for k, v in per_item.items() if k >= 0)
    multi = [f for f in files if f in votes and len([k for k in votes[f] if k >= 0]) > 1]
    print(f'{OUT.relative_to(root)}: {n_items} modules under {len([k for k in per_item if k >= 0])} items, '
          f'{len(out_files)} outside, {len(found_files)} foundation, {len(multi)} multi-item; {len(text):,} chars')


if __name__ == '__main__':
    main()
