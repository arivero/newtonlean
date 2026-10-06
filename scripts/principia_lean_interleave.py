"""Interleave the modern Principia rendering with the Lean theorems anchored to it.

Reads the archived Markdown and Lean sources at a git revision (default HEAD;
WORKTREE includes the uncommitted refactor), and writes
docs/reference/principia-with-lean.md: after each Definition, Law, Lemma,
Proposition or Scholium, every module whose source comments anchor it there is
printed in full, verbatim, in a smaller monospace face (definitions,
docstrings, statements and proofs), in import order.  A module with several
anchors is printed under its first represented item, with a cross-reference
under the others.  Modules with no source anchor (the
foundation) and modules anchored outside the rendered range are printed in
full in two appendices.  Every line of the libraries at the selected revision appears exactly once.

Build the PDF with

    pandoc docs/reference/principia-with-lean.md -o docs/reference/principia-with-lean.pdf \
      --pdf-engine=xelatex -V mainfont="DejaVu Serif" -V monofont="DejaVu Sans Mono" \
      -V mathfont="DejaVu Math TeX Gyre" --toc --toc-depth=2
"""
import argparse
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

from lean_declarations import declarations

root = Path(__file__).resolve().parents[1]
REV = 'HEAD'
SRC = root / 'docs/reference/principia-1687-modern.md'
OUT = root / 'docs/reference/principia-with-lean.md'


def git(*args):
    return subprocess.run(['git', '-C', str(root), *args], capture_output=True,
                          text=True, check=True).stdout


def read_file(path):
    if REV == 'WORKTREE':
        return (root / path).read_text()
    return git('show', f'{REV}:{path}')


def revision_paths():
    if REV == 'WORKTREE':
        return [str(p.relative_to(root)) for library in
                ('NewtonLimitDynamics', 'BarrowLib', 'ClassicsLib', 'ModernLib')
                for p in (root/library).rglob('*.lean')] + [
                    p for p in ('BarrowLib.lean', 'ClassicsLib.lean', 'ModernLib.lean',
                                'NewtonLimitDynamics.lean') if (root/p).is_file()]
    return git('ls-tree', '-r', '--name-only', REV).splitlines()


# ---------------------------------------------------------------- items
# Heading as it appears in the rendering, and the paragraph anchors of that
# item in 1687 (NATP00075/76/77), 1713 (NATP00080/81/82), 1726 (85/86/87)
# and De Motu (NATP00089/90).  Placement is editorial; Scholia are items of
# their own. A source anchor does not assert a proof dependency.

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
    0: "Not encoded. The model has no mass: forces are accelerative (Definition VII). A `mass` parameter appears only in the potential diagnostics (`Diagnostic/DeflectionPotential`, `Diagnostic/QuadraticEndpointPotential`, `Diagnostic/ConstructedHarmonicPotential`).",
    1: "Not encoded; with mass absent, velocity stands in for quantity of motion.",
    2: "Encoded, not proved: the inertial drift `pointAdd s.1 (pointScale d s.2)` that opens every cell (`CentralSchedule.cell`), and `ZeroForce.inertialAt`.",
    3: "Encoded, not proved: the velocity kick `pointAdd s.2 (pointScale d (a y))` of every cell, with the field evaluated at the arrival vertex in `CentralSchedule.cell`; `TimeSubdivision.endKick` is the same kick for a constant acceleration.",
    4: "Encoded as the predicate `CentralSchedule.central` (`det p (a p) = 0`: the force is parallel to the radius) and the `inward` field of `ForceClasses.CentralOracle` (every sample a nonnegative multiple of `-p`).",
    5: "Not encoded.",
    6: "Encoded: a force is a map `Field := Point → Point` from positions to accelerations (`CentralSchedule`), or its rational samples with error (`ForceClasses.Oracle`).",
    7: "Not encoded (no mass).",
    8: "Absolute time is the rational parameter of every schedule and, in the completed layer, the constructed `BinaryTime` quotient; absolute space is the rational plane `Point := Fraction × Fraction` (`BarrowLib/Polygon/PointAlgebra`, in the `TimeSubdivision` namespace). Relative motion appears only as the uniformly moving centre of Proposition II, Case 2.",
    9: "Also encoded as the drift in every cell, and stated as `RelativeMotion.lawI_uniform` (printed under Proposition III, which cites it).",
    10: "Encoded in impulse form by the kick of `CentralSchedule.cell`: the change of velocity is `d · a(y)`, along the force and proportional to it; and by `Finite.EuclideanConstruction.kick`, which displaces the vertex parallel to the radius.",
    11: "Not encoded: the model is single-body. Proposition III cancels the second body's force by Corollary VI, not by Law III.",
    12: "Encoded as `Finite.step g p q j = g.kick q (g.extend p q) j` with the field `same_base_parallels` of `EuclideanConstruction`: the displaced vertex lies on the line through the inertial point parallel to the radius, Newton's parallelogram.",
    13: "Not encoded.",
    14: "Not encoded (no mass, single body).",
    15: "Not encoded.",
    16: "Used as `Converse.moving_centre_equal_areas_central`, Proposition II, Case 2 (printed under Proposition II).",
    17: "Stated and used as `RelativeMotion.corVI_relative` (printed under Proposition III).",
    18: "Not encoded, except that Galileo's parabola is the parallel-force instance `ForceClasses.parallelOracle` and `Polygon/ParallelQuadraticEndpoint`.",
    19: "Encoded as the limit interface of `BarrowLib/Common/Quadratic.lean`: `Near` and `Ultimate` (ultimate equality is approach closer than any given difference), used by `enclosure_reconstruction`, the squeeze; and as the `Within` and `Vanishes` predicates of `CauchyValues` and `Enclosure`.",
    20: "The equal-width rectangle-sum gap is a checked finite partial reconstruction; geometric union-area identification and the ultimate curvilinear ratio remain open.",
    21: "Separate result files own Lemma III and its four corollaries. Maximum-width rectangle gap exhaustion and modern chord/supporting-boundary limits are checked with explicit premises. Scalar area, boundary convergence, tangent identification and the historical ultimate-area passage remain separate.",
    27: "The `Ultimate` conclusions are conditional on `Ultimate` hypotheses (the limit interface transports limits, it does not produce one).",
    28: "`LemmaXPremises` (both editions) is a bundle of `Ultimate` fields whose theorem is their squeeze; no instance is ever built, and the 1713 structure only wraps the 1687 one, so the 1713 force clause has no separate formal content. `MonotoneEnclosure` formalizes that clause on finite cells, unconnected to the theorem.",
    29: "`ContactEnclosure` is likewise a bundle of limit fields with no instance; its docstring says establishing them from an actual curved diagram remains open.",
    31: "The finite central polygon area law is exact. Modern support proves the constructed curve's all-interval swept-fan law and matched-region outer-content decay. The given-motion theorem derives agreement and those laws from explicit local consistency; deriving that consistency from independent motion laws and identifying ordinary sector-union area remain open. The historical AreaLaw file contains separate witness texts and finite proof steps, then an explicitly separated anachronical section. No complete historical limit proof is claimed.",
    32: "Also `CentralSchedule.unequal_cells_converse` (printed under Proposition I): the finite converse for unequal cells.",
    36: "No Lean reconstructs the proposition's proof. `Comparison/CircleCompare` gives the finite sagitta core only, with the 1687 and 1713 limiting routes deliberately not derived; `HarmonicStability` is anchored here by its reference to Corollary 3 though its content serves Proposition I; `InverseCubeAreal` is a diagnostic.",
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

def module_order():
    order = []
    paths = set(revision_paths())
    for lib in ('BarrowLib.lean', 'ClassicsLib.lean', 'ModernLib.lean', 'NewtonLimitDynamics.lean'):
        if lib not in paths:
            continue
        for line in read_file(lib).split('\n'):
            if line.startswith('import '):
                order.append(line[7:].strip().replace('.', '/') + '.lean')
    return {f: i for i, f in enumerate(order)}


ANCHOR = re.compile(r'NATP\d{5}(?:\.par|\s+par)\s*(\d+)')


def source_anchors(source):
    """Paragraphs named in Lean comments; this is editorial placement only."""
    comments = re.findall(r'/-(?:.|\n)*?-/', source)
    anchors = []
    for comment in comments:
        for match in ANCHOR.finditer(comment):
            doc = match.group(0)[:9]
            anchor = f'{doc}.par{match.group(1)}'
            if anchor not in anchors:
                anchors.append(anchor)
    return anchors


# -------------------------------------------------------------------- main

def main():
    global REV, OUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('revision', nargs='?', default='HEAD', help='Git revision or WORKTREE')
    parser.add_argument('--output', type=Path, default=OUT)
    args = parser.parse_args()
    REV, OUT = args.revision, args.output
    order = module_order()
    paths = revision_paths()
    files = sorted((f for f in paths if f.endswith('.lean') and
                    f.startswith(('NewtonLimitDynamics/', 'BarrowLib/', 'ClassicsLib/', 'ModernLib/'))),
                   key=lambda f: (order.get(f, 10_000), f))
    texts = {f: read_file(f) for f in files}
    anchors = {f: source_anchors(texts[f]) for f in files}
    theorem_counts = {f: sum(kind in ('theorem', 'lemma') for kind, *_ in declarations(texts[f]))
                      for f in files}
    referenced = {f: [i for i in range(len(ITEMS))
                      if any(ANCHOR_TO_ITEM.get(a) == i for a in anchors[f])] for f in files}
    home = {f: (referenced[f][0] if referenced[f] else (-1 if anchors[f] else -2))
            for f in files}
    def is_stub(f):
        return all(l.startswith('import ') for l in texts[f].split('\n') if l.strip())
    stubs = [f for f in files if f in texts and is_stub(f)]
    per_item = defaultdict(list)
    for f in files:
        if f in home and f not in stubs:
            per_item[home[f]].append(f)
    # also the two root import files, so that every library line appears
    roots = []
    for lib in ('BarrowLib.lean', 'ClassicsLib.lean', 'ModernLib.lean', 'NewtonLimitDynamics.lean'):
        try:
            texts[lib] = read_file(lib)
            roots.append(lib)
        except subprocess.CalledProcessError:
            pass

    def verbatim(text, size='scriptsize'):
        # Keep the source bytes between delimiters, including final blank lines.
        boundary = '' if text.endswith('\n') else '\n'
        return f'\\begin{{Verbatim}}[breaklines,breakanywhere,fontsize=\\{size}]\n{text}{boundary}\\end{{Verbatim}}\n'

    def render_files(fs, size='scriptsize'):
        parts = []
        for f in fs:
            n = theorem_counts.get(f, 0)
            what = f'{n} theorem{"s" if n != 1 else ""}' if n else 'definitions only'
            parts.append(f'\\noindent{{\\small\\texttt{{{f}}}}}{{\\small, {what}, '
                         f'{texts[f].count(chr(10))} lines}}\n')
            parts.append(verbatim(texts[f], size))
        return '\n'.join(parts)

    def item_block(idx):
        fs = per_item.get(idx, [])
        others = [f for f in files if home[f] != idx and idx in referenced[f] and f not in stubs]
        note = NOTES.get(idx)
        if not fs and not others:
            txt = 'No Lean source module is anchored to this item.'
            if note:
                txt += ' ' + note
            return '\\noindent{\\small\\textit{' + txt.replace('_', '\\_') + '}}\n'
        n = sum(theorem_counts[f] for f in fs)
        head = (f'\\noindent{{\\small\\textit{{Lean reconstruction: {n} theorem{"s" if n != 1 else ""} '
                f'in {len(fs)} module{"s" if len(fs) != 1 else ""} placed at this source item; the modules follow in full, '
                f'in the order of the library import lists (a module may import one printed under another item).}}}}\n')
        if others:
            names = [f'{ITEMS[home[f]][0].strip("*#").strip()} ({f.split("/")[-1]})' for f in others if home[f] >= 0]
            if names:
                head += ('\n\\noindent{\\small\\textit{Also anchored in modules printed under: ' + '; '.join(names) + '.}}\n')
        if note:
            head += '\n\\noindent{\\small\\textit{' + note.replace('_', '\\_') + '}}\n'
        return head + '\n' + render_files(fs)

    # ---- walk the rendering and insert after each item
    lines = read_file(str(SRC.relative_to(root))).split('\n')
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

After each Definition, Law, Lemma, Proposition or Scholium, Lean modules with
comments naming that source item are printed in a smaller monospace face:
definitions, docstrings, statements and proofs, verbatim, in the order of
the library import lists. The source comments give Newton Project paragraph
anchors; a module naming several items is printed under the first represented
item and cross-referenced under the others. This placement is editorial; it
does not show that any theorem proves the item or uses it as a dependency.
Each item collects the anchors of the same
proposition in De Motu, 1687 and 1713, so the stage-local modules
appear together under the 1687 item while keeping their own namespaces. In
the refactored tree, one historical result file contains separate witness
sections; source-only open results are placed by their in-file Latin markers.
Primary proofs use elementary/classical support; anachronical proofs in the
same file follow a five-line separator. Using an anachronical proof taints a
downstream proof transitively through its compiled type or body. This reading
artifact does not inspect compiled proof dependencies. A partial result is
not a completed historical proof. Items with no anchored module say so.
The encoding uses rational arithmetic and Lean 4 core only: it supplies no historical premise,
and its appearance under an item records that the item motivated it, not that
the item is thereby proved. Two appendices print, in full, the modules
anchored outside the rendered range and the foundation modules with no source
anchor, which are most of the code. Every line of the libraries appears
exactly once; the verification harnesses under `research/verification` are
not included.
"""
    text = '\n'.join(out)
    text = text.replace('\n## How the editions differ', intro + '\n## How the editions differ', 1)

    # ---- appendices
    out_files = per_item.get(-1, [])
    found_files = per_item.get(-2, [])
    n_out = sum(theorem_counts[f] for f in out_files)
    n_found = sum(theorem_counts[f] for f in found_files)
    text += '\n\n# Appendix A. Modules anchored outside Sections I–II\n\n'
    text += (f'{len(out_files)} module{"s" if len(out_files) != 1 else ""} with {n_out} theorems '
             'name source paragraphs outside the rendered range.\n\n')
    text += render_files(out_files)
    text += '\n\n# Appendix B. The foundation: modules with no source anchor\n\n'
    text += (f'{len(found_files)} modules with {n_found} theorems have no Newton anchor. They build the rational '
             'arithmetic, point algebra, finite estimates, Cauchy names and quotient values, binary time, '
             'square covers and the lifting of operations to completed values on which the anchored proofs '
             'stand. In full, in import order, followed by the available library root files.\n\n')
    text += render_files(found_files + roots)
    text += '\n\n## Compatibility import stubs\n\n'
    text += (f'{len(stubs)} library files consist only of imports and keep old module '
             'names valid after library migration. They are not counted as modules above.\n\n')
    text += render_files(stubs)
    OUT.write_text(text.rstrip('\n') + '\n')
    n_items = sum(len(v) for k, v in per_item.items() if k >= 0)
    multi = [f for f in files if len(referenced[f]) > 1]
    print(f'{OUT}: {n_items} modules under {len([k for k in per_item if k >= 0])} items, '
          f'{len(out_files)} outside, {len(found_files)} foundation, {len(multi)} multi-item; {len(text):,} chars')


if __name__ == '__main__':
    main()
