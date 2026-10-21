#!/usr/bin/env bash
# Citation gate (docs/REFACTOR_PLAN.md, citation convention).
#
#   scripts/CheckCitations.sh
#
# Checks every Lean file under Feec/:
# 1. every bracketed citation key `[Key]` (Key = AuthorYear, e.g. `[QuennevilleBelair2015]`,
#    `[AFW2010]`) has an entry in docs/references.bib;
# 2. no citation carries its location inside the brackets (`[Key, Prop 4.17]`): doc-gen4 reads
#    the whole bracket as the key, so the location goes outside, `[Key], Prop 4.17`;
# 3. no `Thesis:` tag (retired; thesis traceability is `[QuennevilleBelair2015], Prop 4.17`);
# 4. every module docstring has a `## References` section, and every key cited anywhere in the
#    file has an entry there of the form `* [Author(s), *Title*][Key]` (optionally followed by
#    a location), with the authors (initials and last names) and the title of docs/references.bib;
# 5. every module docstring declares its bibliography on a line of its own,
#    `Bibliography: [references.bib](<path>)`, with <path> the relative path from the file to
#    docs/references.bib, so that leantex (and doc-gen4) resolve the citations.
#
# Exit status: nonzero if any check fails; each failure is printed as `path:line: message`.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -I - <<'EOF'
import os, pathlib, re, sys

# --- docs/references.bib: key -> (authors, title) as displayed in `## References` ---
ACC = {"\\'": {'e': 'é', 'a': 'á', 'E': 'É', 'o': 'ó', 'i': 'í'}, '\\"': {'u': 'ü', 'o': 'ö', 'a': 'ä'},
       '\\`': {'e': 'è', 'a': 'à'}, '\\v': {'s': 'š', 'c': 'č', 'r': 'ř', 'z': 'ž'}}
def delatex(s):
    s = s.replace('{$L^2$}', 'L²').replace('{$L_2$}', 'L₂')
    acc = lambda m: ACC[m.group(1)][m.group(2)]
    s = re.sub(r'\{(\\[\'"`]|\\v)\{?([A-Za-z])\}?\}', acc, s)
    s = re.sub(r'(\\[\'"`])\{?([A-Za-z])\}?', acc, s)
    return ' '.join(s.replace('--', '–').replace('{', '').replace('}', '').split())
def field(body, name):
    m = re.search(r'\b' + name + r'\s*=\s*\{', body)
    if not m:
        return ''
    i = j = m.end(); d = 1
    while d:
        d += {'{': 1, '}': -1}.get(body[j], 0); j += 1
    return body[i:j - 1]
def initials(first):
    return ' '.join(w if (w.endswith('.') and len(w) <= 3)
                    else '-'.join(p[0] + '.' for p in w.split('-')) for w in first.split())
def person(a):
    p = [x.strip() for x in a.split(',')]
    return f'{initials(p[2])} {p[0]}, {p[1]}' if len(p) == 3 else f'{initials(p[1])} {p[0]}'
src = pathlib.Path('docs/references.bib').read_text(encoding='utf-8')
bib = {}
for m in re.finditer(r'@(\w+)\{([^,\s]+),', src):
    nxt = src.find('\n@', m.end()); body = src[m.end(): nxt if nxt >= 0 else len(src)]
    au = delatex(field(body, 'author'))
    bib[m.group(2)] = (', '.join(person(x) for x in re.split(r'\s+and\s+', au)) if au else '',
                       delatex(field(body, 'title')))

KEY = r'[A-Z][A-Za-z\-]*\d{4}[a-z]?'
CITE = re.compile(r'\[(' + KEY + r')\](?!\()')
INSIDE = re.compile(r'\[(' + KEY + r'),')
ENTRY = re.compile(r'^\* \[([^\[\]]*), \*([^*]+)\*\]\[(' + KEY + r')\]', re.M)
errors = []
files = [pathlib.Path('Feec.lean')] + sorted(pathlib.Path('Feec').rglob('*.lean'))
line = lambda s, i: s.count('\n', 0, i) + 1
for f in files:
    s = f.read_text(encoding='utf-8')
    for m in CITE.finditer(s):
        if m.group(1) not in bib:
            errors.append(f'{f}:{line(s, m.start())}: citation key [{m.group(1)}] has no entry in '
                          'docs/references.bib')
    for m in INSIDE.finditer(s):
        errors.append(f'{f}:{line(s, m.start())}: location inside the brackets ([{m.group(1)}, ...]); '
                      f'write [{m.group(1)}], ...')
    for m in re.finditer(r'\bThesis:', s):
        errors.append(f'{f}:{line(s, m.start())}: `Thesis:` tag; write [QuennevilleBelair2015], ...')
    i = s.find('/-!')
    j = s.find('-/', i) if i >= 0 else -1
    k = s.find('## References', i, j) if i >= 0 else -1
    rel = os.path.relpath('docs/references.bib', f.parent)
    decl = f'Bibliography: [references.bib]({rel})'
    if i < 0 or not re.search(r'^' + re.escape(decl) + r'$', s[i:j], re.M):
        errors.append(f'{f}:1: module docstring lacks the line `{decl}`')
    if k < 0:
        errors.append(f'{f}:1: module docstring has no `## References` section')
        continue
    listed = {}
    for m in ENTRY.finditer(s, k, j):
        key, au, ti = m.group(3), m.group(1), m.group(2)
        listed[key] = True
        if key in bib and (au, ti) != bib[key]:
            errors.append(f'{f}:{line(s, m.start())}: reference entry for [{key}] should read '
                          f'`* [{bib[key][0]}, *{bib[key][1]}*][{key}]`')
    for key in dict.fromkeys(CITE.findall(s)):
        if key not in listed:
            errors.append(f'{f}:{line(s, k)}: [{key}] is cited but has no `* [Author(s), *Title*][{key}]` '
                          'entry in `## References`')
for e in errors:
    print(e)
print(f'CheckCitations: {len(files)} files, {len(bib)} bib entries, {len(errors)} errors')
sys.exit(1 if errors else 0)
EOF
