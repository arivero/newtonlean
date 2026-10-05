"""Count Lean theorems at every commit and plot the project's progress.

Walks the git history oldest first and parses every tracked `.lean` file at
each commit.  A theorem is keyed by its namespace-qualified name, so a moved
or re-exported theorem keeps its identity; a private -> public switch counts
as a visibility change.  Statements are compared up to the first `:=`, with
comments and whitespace ignored, so a docstring edit is not a change.

Library theorems are those under NewtonLimitDynamics/ or BarrowLib/. Theorems in
research/verification/ are holdout/comparator harnesses and are counted
separately.

Each library theorem is also classified heuristically (see `classify`):
  duplicate    its statement repeats an earlier theorem's, up to variable names
               (stage-local restatements of one finite result count once)
  sample       a check on specific numbers (counterexamples are kept)
  plumbing     it mentions only Fraction/Point arithmetic, det/dot, numeric
               constants and generic list sums
  substantive  everything else
The classification reads statements only; it cannot judge depth or relevance.

Outputs (docs/progress/):
  history.csv                   one row per commit (the table view of the plots)
  theorems-total[-dark].svg     cumulative theorems, substantive theorems, definitions
  theorems-churn[-dark].svg     added / modified / deleted per commit
  theorems-by-area[-dark].svg   cumulative theorems by proof obligation
  completion[-dark].svg         editorial completion estimate, from
                                completion-estimate.json

Requires matplotlib.  The completion figure plots a judgement recorded in
completion-estimate.json; edit that file, not this script, to revise it.
"""
import csv
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402

root = Path(__file__).resolve().parents[1]
out_dir = root / 'docs/progress'
out_dir.mkdir(parents=True, exist_ok=True)


def git(*args):
    return subprocess.run(['git', '-C', str(root), *args], capture_output=True,
                          text=True, check=True).stdout


# ---------------------------------------------------------------- parsing

from lean_declarations import declarations, DEF_KINDS


# ------------------------------------------------------- obligation groups

# Stacked bottom to top in this order; colours follow the same order.
GROUPS = [
    ('stage', 'Stage-local, M1–M4 support, shared arithmetic'),
    ('finite', 'Finite joining & refinement (orders 2–3)'),
    ('props24', 'Props. II–IV finite steps (orders 5–7)'),
    ('prop1', 'Prop. I realization (order 4)'),
    ('action', 'Action diagnostic (order 8)'),
]
FINITE = {'Contact', 'RefinementStrip', 'TimeSubdivision', 'PartitionControl', 'PartialCell',
          'UniformRefinement', 'PartitionComparison', 'StripArea', 'ZeroForce',
          'InertialControl', 'InertialDefect'}
PROP1 = {'CentralSchedule', 'PathDefect', 'PointBounds', 'TriangleBounds', 'ConvexCover',
         'CauchyValues', 'BinaryTime', 'PositionValues', 'FiniteEstimates', 'FiniteAccumulation', 'BoundedIteration', 'ForceClasses',
         'StateDistance', 'EndpointCauchyName', 'DyadicArithmetic', 'FinitePower', 'GeometricTail',
         'ScaledTolerance', 'AffineValues', 'IntegerRefinement', 'BinaryCells', 'AffineBoundary', 'IntegerSchedule', 'FiniteAddress', 'FiniteRecurrence', 'IntegerTime'}


def group_of(path):
    parts = Path(path).with_suffix('').parts
    area, stem = (parts[1], parts[-1]) if len(parts) >= 3 else ('', parts[-1])
    if area == 'Diagnostic' or stem == 'MonotoneEnclosure':
        return 'action'
    if stem in ('Converse', 'RelativeMotion', 'CircleCompare'):
        return 'props24'
    if stem.startswith('Harmonic') or stem in PROP1 or stem == 'FiniteGrowth':
        return 'prop1'
    if area == 'Polygon' and (stem in FINITE or stem == 'PointAlgebra'):
        return 'finite'
    return 'stage'


# ----------------------------------------------------------- classification

# Library definitions whose use alone marks a statement as arithmetic plumbing.
ARITH = {
    'Fraction', 'Point', 'LatticePoint', 'equiv', 'le', 'lt', 'add', 'sub', 'mul', 'neg', 'ofInt',
    'abs', 'half', 'positive', 'fracNeg', 'det', 'dot', 'pointAdd', 'pointSub', 'pointNeg',
    'pointScale', 'pointEquiv', 'pointNorm', 'stateNorm', 'stateSub', 'stateEquiv', 'latticeAdd',
    'zeroPoint', 'zero', 'one', 'two', 'three', 'four', 'quarter', 'eighth', 'negQuarter',
    'Nonnegative', 'weightSum', 'factorProduct', 'amplification', 'nsum', 'isum',
}
IDENT = re.compile(r"[A-Za-z_][\w']*")
DOTTED = re.compile(r"(?<![\w.'])[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")


def statement_key(stmt, own_defs, namespaces):
    """Statement with binder names renamed positionally and every library
    definition resolved to `name@namespace`, so same-named definitions in
    different modules stay distinct.  own_defs maps the theorem file's
    definitions to their namespaces; namespaces maps each definition name to
    all namespaces defining it."""
    s = re.sub(r'^(?:theorem|lemma)\s+\S+', '', stmt).strip()
    names = []
    for group in re.findall(r'[({\[]([^(){}\[\]:]+):', s):
        names += [v for v in group.split() if IDENT.fullmatch(v) and v not in names]
    for i, v in enumerate(names):
        s = re.sub(rf"(?<![\w.']){re.escape(v)}(?![\w'])", f'_{i}', s)

    def resolve(m):
        parts = m[0].split('.')
        for k in range(len(parts) - 1, 0, -1):  # qualified reference, e.g. Fraction.add
            short, qualifier = parts[k], '.'.join(parts[:k])
            hits = [ns for ns in namespaces.get(short, ()) if ns == qualifier or ns.endswith('.' + qualifier)]
            if hits:
                return f'{short}@{hits[0]}' + ''.join('.' + p for p in parts[k + 1:])
        head = parts[0]
        if head in own_defs:
            ns = own_defs[head]
        elif len(namespaces.get(head, ())) == 1:
            ns = next(iter(namespaces[head]))
        elif head in namespaces:
            ns = '?'
        else:
            return m[0]
        return f'{head}@{ns}' + ''.join('.' + p for p in parts[1:])
    s = DOTTED.sub(resolve, s)
    return ' '.join(s.split())


def classify(theorems, defs_by_file):
    """Count duplicate / sample / plumbing / substantive among (file, name, stmt).
    defs_by_file maps each file to {definition name: namespace}."""
    namespaces = {}
    for defs in defs_by_file.values():
        for short, ns in defs.items():
            namespaces.setdefault(short, set()).add(ns)
    seen, counts = set(), Counter()
    for f, name, stmt in sorted(theorems, key=lambda t: t[0]):
        key = statement_key(stmt, defs_by_file.get(f, {}), namespaces)
        short = name.split('.')[-1] if name else ''
        refs = set(re.findall(r"([A-Za-z_][\w']*)@", key))
        if key in seen:
            counts['duplicate'] += 1
            continue
        seen.add(key)
        counterexample = 'counterexample' in short
        closed = key.startswith(':') and not re.search('[∀∃¬]', key)
        if not counterexample and ('sample' in short or re.search(r'(^|_)example', short) or closed):
            counts['sample'] += 1
        elif refs <= ARITH:
            counts['plumbing'] += 1
        else:
            counts['substantive'] += 1
    return counts


# ------------------------------------------------------------ history walk

def walk():
    fmt = '%H%x09%h%x09%aI%x09%s'
    rows, prev = [], {}
    for idx, line in enumerate(git('log', '--topo-order', '--reverse', f'--format={fmt}')
                               .strip().split('\n'), start=1):
        full, sha, date, subject = line.split('\t', 3)
        files = [f for f in git('ls-tree', '-r', '--name-only', full).split('\n')
                 if f.endswith('.lean') and f != 'lakefile.lean']
        cur, defs, lines, harness = {}, 0, 0, 0
        groups = Counter()
        located, defs_by_file = [], {}
        for f in files:
            library = f.startswith(('NewtonLimitDynamics', 'BarrowLib'))
            src = git('show', f'{full}:{f}')
            if library:
                lines += src.count('\n')
            for kind, name, stmt, body, private in declarations(src):
                if kind in ('theorem', 'lemma'):
                    if not library:
                        harness += 1
                        continue
                    key, n = name or f'{f}::anon', 2
                    while key in cur:
                        key, n = f'{name}#{n}', n + 1
                    cur[key] = (stmt, body, private)
                    located.append((f, name, stmt))
                    groups[group_of(f)] += 1
                elif kind in DEF_KINDS and library:
                    defs += 1
                    if name:
                        ns, _, short = name.rpartition('.')
                        defs_by_file.setdefault(f, {})[short] = ns
        kinds = classify(located, defs_by_file)
        common = [k for k in cur if k in prev]
        row = {
            'index': idx, 'commit': sha, 'date': date, 'subject': subject,
            'theorems': len(cur),
            'added': sum(k not in prev for k in cur),
            'deleted': sum(k not in cur for k in prev),
            'statement_changed': sum(cur[k][0] != prev[k][0] for k in common),
            'proof_changed': sum(cur[k][0] == prev[k][0] and cur[k][1] != prev[k][1] for k in common),
            'visibility_changed': sum(cur[k][2] != prev[k][2] for k in common),
            'definitions': defs, 'library_lines': lines, 'harness_theorems': harness,
            'substantive': kinds['substantive'], 'plumbing': kinds['plumbing'],
            'sample': kinds['sample'], 'duplicate': kinds['duplicate'],
        }
        row['modified'] = row['statement_changed'] + row['proof_changed'] + row['visibility_changed']
        for g, _ in GROUPS:
            row[f'group_{g}'] = groups[g]
        rows.append(row)
        prev = cur
    return rows


# ----------------------------------------------------------------- theming

THEMES = {
    'light': dict(surface='#fcfcfb', ink='#0b0b0b', ink2='#52514e', muted='#898781',
                  grid='#e1e0d9', axis='#c3c2b7', track='#f0efec',
                  series=['#2a78d6', '#eb6834', '#1baf7a', '#eda100', '#e87ba4'],
                  added='#2a78d6', modified='#eb6834', deleted='#e34948'),
    'dark': dict(surface='#1a1a19', ink='#ffffff', ink2='#c3c2b7', muted='#898781',
                 grid='#2c2c2a', axis='#383835', track='#2c2c2a',
                 series=['#3987e5', '#d95926', '#199e70', '#c98500', '#d55181'],
                 added='#3987e5', modified='#d95926', deleted='#e66767'),
}


def setup(theme, size):
    t = THEMES[theme]
    plt.rcParams.update({
        'svg.fonttype': 'none', 'svg.hashsalt': 'newtonlean',
        'font.family': 'sans-serif',
        'font.sans-serif': ['Inter', 'Helvetica Neue', 'Arial', 'DejaVu Sans'],
        'font.size': 10, 'axes.titlesize': 12, 'axes.titleweight': 'bold',
        'axes.titlelocation': 'left', 'axes.titlepad': 14,
        'text.color': t['ink'], 'axes.labelcolor': t['ink2'],
        'xtick.color': t['muted'], 'ytick.color': t['muted'],
        'axes.edgecolor': t['axis'], 'axes.facecolor': t['surface'],
        'figure.facecolor': t['surface'], 'savefig.facecolor': t['surface'],
        'axes.grid': True, 'grid.color': t['grid'], 'grid.linewidth': 0.8,
        'axes.axisbelow': True, 'axes.spines.top': False, 'axes.spines.right': False,
        'legend.frameon': False, 'legend.labelcolor': t['ink2'],
    })
    fig, ax = plt.subplots(figsize=size)
    return t, fig, ax


def session_ticks(ax, rows, gap_hours=24):
    """Tick the first commit of each work session (sessions split at gaps > gap_hours)."""
    from datetime import datetime
    months = {9: 'Sep', 10: 'Oct', 11: 'Nov', 12: 'Dec'}
    sessions, last = [], None
    for r in rows:
        when = datetime.fromisoformat(r['date'])
        if last is None or (when - last).total_seconds() > gap_hours * 3600:
            sessions.append([r['index'], when, when])
        sessions[-1][2] = when
        last = when

    def label(a, b):
        if a.date() == b.date():
            return f'{a.day} {months[a.month]}'
        if a.month == b.month:
            return f'{a.day}–{b.day} {months[a.month]}'
        return f'{a.day} {months[a.month]}–{b.day} {months[b.month]}'
    ax.set_xticks([s[0] for s in sessions], [label(s[1], s[2]) for s in sessions])
    ax.set_xlim(0.5, rows[-1]['index'] + 0.5)
    ax.set_xlabel('Commit, oldest first (ticks mark the first commit of each work session)')


def save(fig, name, theme):
    suffix = '' if theme == 'light' else '-dark'
    fig.tight_layout()
    path = out_dir / f'{name}{suffix}.svg'
    fig.savefig(path, metadata={'Date': None})
    plt.close(fig)
    # matplotlib leaves trailing spaces in path data; keep `git diff --check` clean.
    path.write_text('\n'.join(line.rstrip() for line in path.read_text().split('\n')))


# ------------------------------------------------------------------- charts

def plot_total(rows, theme):
    t, fig, ax = setup(theme, (9, 4.2))
    x = [r['index'] for r in rows]
    for key, label, colour in (('theorems', 'Theorems', t['series'][0]),
                               ('substantive', 'Substantive theorems (heuristic)', t['series'][2]),
                               ('definitions', 'Definitions and structures', t['series'][1])):
        y = [r[key] for r in rows]
        ax.plot(x, y, color=colour, lw=2, solid_joinstyle='round', solid_capstyle='round', label=label)
        ax.plot(x[-1], y[-1], 'o', ms=8, color=colour, mec=t['surface'], mew=2)
        ax.annotate(f'{y[-1]:,}', (x[-1], y[-1]), xytext=(8, 0), textcoords='offset points',
                    va='center', color=t['ink'], fontweight='bold')
    last = rows[-1]
    ax.set_title(f"Lean library declarations per commit: {last['theorems']:,} theorems, "
                 f"{last['substantive']:,} substantive, at {last['commit']}")
    ax.set_ylabel('Count at commit')
    ax.set_ylim(0, None)
    ax.legend(loc='upper left')
    session_ticks(ax, rows)
    ax.set_xlim(0.5, rows[-1]['index'] + 4)
    save(fig, 'theorems-total', theme)


def plot_churn(rows, theme):
    t, fig, ax = setup(theme, (9, 4.2))
    x = [r['index'] for r in rows]
    added = [r['added'] for r in rows]
    modified = [r['modified'] for r in rows]
    deleted = [-r['deleted'] for r in rows]
    w = 0.72
    ax.bar(x, added, w, color=t['added'], label='Added', edgecolor=t['surface'], linewidth=0.6)
    ax.bar(x, modified, w, bottom=added, color=t['modified'], edgecolor=t['surface'], linewidth=0.6,
           label='Modified (statement, proof or visibility)')
    ax.bar(x, deleted, w, color=t['deleted'], label='Deleted', edgecolor=t['surface'], linewidth=0.6)
    ax.axhline(0, color=t['axis'], lw=1)
    peak = max(rows, key=lambda r: r['added'])
    ax.annotate(f"+{peak['added']}", (peak['index'], peak['added'] + peak['modified']),
                xytext=(0, 4), textcoords='offset points', ha='center', color=t['ink'], fontweight='bold')
    tot_a = sum(added)
    tot_m = sum(modified)
    tot_d = -sum(deleted)
    ax.set_title(f'Theorem churn per commit: {tot_a:,} added, {tot_m} modified, {tot_d} deleted')
    ax.set_ylabel('Theorems')
    ax.legend(loc='upper left')
    session_ticks(ax, rows)
    save(fig, 'theorems-churn', theme)


def plot_groups(rows, theme):
    t, fig, ax = setup(theme, (9, 4.6))
    x = [r['index'] for r in rows]
    ys = [[r[f'group_{g}'] for r in rows] for g, _ in GROUPS]
    labels = [f'{label} ({y[-1]})' for (_, label), y in zip(GROUPS, ys)]
    ax.stackplot(x, *ys, colors=t['series'][:len(GROUPS)], labels=labels,
                 edgecolor=t['surface'], linewidth=1.2, alpha=0.9)
    ax.set_title('Library theorems by proof obligation (TASKS.md order), cumulative')
    ax.set_ylabel('Theorems at commit')
    ax.set_ylim(0, None)
    handles, labs = ax.get_legend_handles_labels()
    ax.legend(handles[::-1], labs[::-1], loc='upper left')
    session_ticks(ax, rows)
    save(fig, 'theorems-by-area', theme)


def completion_numbers(est):
    def overall(weights):
        props = sum(tg['weight'] * sum(weights[m] * tg['scores'][m] for m in weights)
                    for tg in est['targets'])
        return props + est['action_diagnostic']['weight'] * est['action_diagnostic']['score']
    base = {m: v['weight'] for m, v in est['milestones'].items()}
    alts = [overall(w) for w in est['alternative_weightings'].values()]
    return overall(base), min(alts + [overall(base)]), max(alts + [overall(base)])


def plot_completion(est, theme):
    t, fig, ax = setup(theme, (9, 3.6))
    milestones = list(est['milestones'].items())
    rows = est['targets'] + [{'label': est['action_diagnostic']['label'], 'action': True}]
    y = list(range(len(rows)))[::-1]
    for yi, tg in zip(y, rows):
        ax.barh(yi, 100, 0.5, color=t['track'], edgecolor='none')
        left = 0.0
        if tg.get('action'):
            share = 100 * est['action_diagnostic']['score']
            ax.barh(yi, share, 0.5, left=0, color=t['series'][4], edgecolor=t['surface'], linewidth=1.5)
            left = share
        else:
            for i, (m, spec) in enumerate(milestones):
                share = 100 * spec['weight'] * tg['scores'][m]
                if share > 0:
                    ax.barh(yi, share, 0.5, left=left, color=t['series'][i], edgecolor=t['surface'],
                            linewidth=1.5, label=spec['label'] if yi == y[0] else None)
                left += share
        ax.text(left + 1.2, yi, f'{left:.0f}%', va='center', color=t['ink'], fontweight='bold')
    ax.set_yticks(y, [tg['label'] for tg in rows])
    ax.tick_params(axis='y', colors=t['ink2'], length=0)
    ax.set_xlim(0, 100)
    ax.set_xticks([0, 25, 50, 75, 100], ['0%', '25%', '50%', '75%', '100%'])
    ax.grid(axis='y', visible=False)
    ax.spines['left'].set_visible(False)
    mid, lo, hi = completion_numbers(est)
    ax.set_title(f'Estimated completion: about {mid * 100:.0f}% overall '
                 f'(range {lo * 100:.0f}–{hi * 100:.0f}%)')
    ax.legend(loc='upper center', bbox_to_anchor=(0.5, -0.14), ncol=4, handlelength=1.2)
    save(fig, 'completion', theme)


# --------------------------------------------------------------------- main

def main():
    rows = walk()
    with open(out_dir / 'history.csv', 'w', newline='') as fh:
        writer = csv.DictWriter(fh, fieldnames=list(rows[0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)
    est = json.loads((out_dir / 'completion-estimate.json').read_text())
    for theme in THEMES:
        plot_total(rows, theme)
        plot_churn(rows, theme)
        plot_groups(rows, theme)
        plot_completion(est, theme)
    last = rows[-1]
    mid, lo, hi = completion_numbers(est)
    print(f"{len(rows)} commits; {last['theorems']} library theorems at {last['commit']} "
          f"(+{sum(r['added'] for r in rows)} / -{sum(r['deleted'] for r in rows)} / "
          f"~{sum(r['modified'] for r in rows)} modified); {last['harness_theorems']} harness theorems")
    print('by obligation:', {g: last[f'group_{g}'] for g, _ in GROUPS})
    print('by kind:', {k: last[k] for k in ('substantive', 'plumbing', 'sample', 'duplicate')})
    print(f'estimated completion {mid:.1%} (range {lo:.1%}-{hi:.1%})')


if __name__ == '__main__':
    main()
