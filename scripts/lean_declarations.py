"""Shared bounded Lean declaration reader for catalogue and progress.

This is a source inventory, not a Lean parser or proof verifier.
"""
import re

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive|instance|example|axiom|opaque|class)'
                  r'\b\s*([^\s:({\[]*)')
TOPCMD = re.compile(r'^(?:@\[|theorem\b|lemma\b|def\b|abbrev\b|structure\b|inductive\b|instance\b|'
                    r'example\b|axiom\b|opaque\b|class\b|namespace\b|end\b|section\b|open\b|'
                    r'variable\b|private\b|protected\b|noncomputable\b|set_option\b|#|import\b|'
                    r'attribute\b|mutual\b|universe\b|macro\b|syntax\b|notation\b|infix)')
VISIBILITY = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private|protected)\s+')
DEF_KINDS = {'def', 'abbrev', 'structure', 'inductive', 'class', 'opaque'}


def strip_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and src.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if src[i] == '\n':
                out.append('\n')
            i += 1
        elif src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)


def declarations(src):
    """Yield (kind, qualified_name, statement, body, private) for top-level declarations."""
    ns = []        # namespace components; None marks an anonymous section
    cur = None
    for line in strip_comments(src).split('\n'):
        line = line.rstrip()
        if line and not line[0].isspace() and TOPCMD.match(line):
            if cur:
                yield finish(cur)
                cur = None
            m = DECL.match(line)
            if m:
                kind, name = m.group(2), m.group(3)
                qual = '.'.join([x for x in ns if x] + [name]) if name else None
                cur = {'kind': kind, 'name': qual, 'lines': [line],
                       'private': 'private' in (m.group(1) or '')}
                continue
            words = line.split()
            if words[0] == 'namespace' and len(words) > 1:
                ns.extend(words[1].split('.'))
            elif words[0] == 'section':
                ns.append(None)
            elif words[0] == 'end' and ns:
                if len(words) > 1 and ns[-1] is not None:
                    for _ in words[1].split('.'):
                        if ns and ns[-1] is not None:
                            ns.pop()
                else:
                    ns.pop()
        elif cur is not None:
            cur['lines'].append(line)
    if cur:
        yield finish(cur)


def statement_prefix(src):
    """Find the body at an unnested := or an equation-style case line."""
    depth = 0
    quoted = False
    escaped = False
    i = 0
    while i < len(src):
        c = src[i]
        if quoted:
            if escaped:
                escaped = False
            elif c == '\\':
                escaped = True
            elif c == '"':
                quoted = False
        elif c == '"':
            quoted = True
        elif c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0 and src.startswith(':=', i):
            return src[:i]
        elif depth == 0 and c == '\n':
            m = re.match(r'\s*\|', src[i + 1:])
            if m:
                return src[:i]
        i += 1
    return src


def finish(cur):
    source = VISIBILITY.sub('', '\n'.join(cur['lines']))
    body = ' '.join(source.split())
    statement = ' '.join(statement_prefix(source).split())
    return cur['kind'], cur['name'], statement, body, cur['private']


