#!/usr/bin/env bash
# Regenerate docs/THESIS_MAP.md: thesis result -> current Lean declarations.
#
#   scripts/ThesisMap.sh [OUT]          (default OUT = docs/THESIS_MAP.md)
#
# Requires an up-to-date `lake build Feec`. Sources, per declaration of a Feec.* module:
#   * its name: a last component containing thm_N_M / prop_N_M / cor_N_M / lemma_N_M (or the
#     compact forms prop417, thm43), ch6_*, Sol61, Hyp54, Sys56, C55;
#   * module sources: any `[QuennevilleBelair2015, ...]` citation lists the module;
#   * its docstring: a `Thesis: Prop 4.17 (corrected), Thm 4.3` tag, and every result, equation,
#     section or chapter cited inside `[QuennevilleBelair2015, ...]`.
# Rerun after renames: entries follow the declarations as long as the new declarations carry a
# `Thesis:` tag or a `[QuennevilleBelair2015, ...]` citation in their docstring.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT="${1:-docs/THESIS_MAP.md}"
if [[ -n "${FEEC_DOCDUMP_IN:-}" ]]; then   # reuse an existing dump (debugging)
  DOCS="$(mktemp /tmp/feec_docdump.XXXXXX.tsv)"; cp "$FEEC_DOCDUMP_IN" "$DOCS"
else
  DOCS="$(mktemp /tmp/feec_docdump.XXXXXX.tsv)"
  FEEC_DOCDUMP_OUT="$DOCS" lake env lean scripts/DocDump.lean
fi
python3 - "$DOCS" "$OUT" <<'EOF'
import re, sys
from collections import defaultdict
docs, out = sys.argv[1:3]

KIND = {'thm': 'Thm', 'theorem': 'Thm', 'prop': 'Prop', 'proposition': 'Prop',
        'cor': 'Cor', 'corollary': 'Cor', 'lemma': 'Lemma', 'remark': 'Remark',
        'def': 'Def', 'definition': 'Def'}
ORDER = {'Thm': 0, 'Prop': 0, 'Cor': 0, 'Lemma': 0, 'Remark': 0, 'Def': 0,
         'Eq': 1, 'Sec': 2, 'Ch': 3}
NUM = r'\d+\.\d+'
RES = re.compile(r'\b(Theorem|Thm|Proposition|Prop|Corollary|Cor|Lemma|Remark|Definition|Def)s?\.?'
                 r'\s+(' + NUM + r'(?:\s*(?:–|-|,|and)\s*' + NUM + r')*)')
EQ = re.compile(r'\((\d+\.\d+)([a-z](?:–[a-z])?)?\)(?:\s*–\s*\((\d+\.\d+)\))?')
SEC = re.compile(r'§\s*(\d+\.\d+)(?:\s*–\s*(\d+\.\d+))?')
CH = re.compile(r'\bCh\.\s*(\d+)\b')
CITE = re.compile(r'\[QuennevilleBelair2015,([^\]]*)\]')
TAG = re.compile(r'\bThesis:\s*((?:[^;\n.]|\.(?=\d))*)')
NAMED = re.compile(r'(?:^|_)(thm|prop|cor|lemma)_(\d+)_(\d+)|(?:^|_)(thm|prop|cor|lemma)(\d)(\d+)(?![\d])')
CHN = re.compile(r'(?:^|_)ch(\d+)_')
OTHER = re.compile(r'^(Sol|Hyp|Sys|C)(\d)(\d+)$')

def key(i):
    k, n = i.split(' ', 1)
    nums = [int(x) for x in re.findall(r'\d+', n)]
    return (ORDER.get(k, 9), nums, k, n)

def expand(kind, s):
    """'4.16–4.18' -> 4.16, 4.17, 4.18; '4.17 and 4.19' -> both."""
    ids = []
    parts = re.split(r'\s*(–|-|,|and)\s*', s)
    prev = None
    i = 0
    while i < len(parts):
        p = parts[i]
        if re.fullmatch(NUM, p):
            if prev and i >= 2 and parts[i - 1] in ('–', '-'):
                a, b = prev.split('.'), p.split('.')
                if a[0] == b[0]:
                    ids += [f'{kind} {a[0]}.{j}' for j in range(int(a[1]) + 1, int(b[1]) + 1)]
                else:
                    ids.append(f'{kind} {p}')
            else:
                ids.append(f'{kind} {p}')
            prev = p
        i += 1
    return ids

def cited(text):
    ids = set()
    for m in RES.finditer(text):
        ids.update(expand(KIND[m.group(1).lower()], m.group(2)))
    for m in EQ.finditer(text):
        ids.add(f'Eq ({m.group(1)})')
        if m.group(3):
            a, b = m.group(1).split('.'), m.group(3).split('.')
            if a[0] == b[0]:
                ids.update(f'Eq ({a[0]}.{j})' for j in range(int(a[1]), int(b[1]) + 1))
    for m in SEC.finditer(text):
        ids.add(f'Sec §{m.group(1)}')
        if m.group(2):
            a, b = m.group(1).split('.'), m.group(2).split('.')
            if a[0] == b[0]:
                ids.update(f'Sec §{a[0]}.{j}' for j in range(int(a[1]), int(b[1]) + 1))
    for m in CH.finditer(text):
        ids.add(f'Ch {m.group(1)}')
    return ids

named = defaultdict(set)   # id -> names (numbered names)
tagged = defaultdict(set)  # id -> names (Thesis: tag)
cites = defaultdict(set)   # id -> names (docstring citation)
mods = defaultdict(set)    # id -> modules
for line in open(docs, encoding='utf-8'):
    line = line.rstrip('\n')
    if not line:
        continue
    name, mod, doc = line.split('\t', 2)
    for c in CITE.findall(doc):
        for i in cited(c):
            cites[i].add(name); mods[i].add(mod)
    for t in TAG.findall(doc):
        for i in cited(t):
            tagged[i].add(name); mods[i].add(mod)

# modules whose source (module docstrings, comments) cites an id
import pathlib
for f in sorted(pathlib.Path('Feec').rglob('*.lean')):
    mod = '.'.join(f.with_suffix('').parts)
    for c in CITE.findall(f.read_text(encoding='utf-8')):
        for i in cited(' '.join(c.split())):
            mods[i].add(mod)

# numbered names: every Feec declaration, with or without a docstring
for line in open('docs/migration/old_theorems.tsv', encoding='utf-8'):
    name = line.split('\t', 1)[0]
    last = name.split('.')[-1]
    for m in NAMED.finditer(last):
        if m.group(1):
            i = f'{KIND[m.group(1)]} {m.group(2)}.{m.group(3)}'
        else:
            i = f'{KIND[m.group(4)]} {m.group(5)}.{m.group(6)}'
        named[i].add(name)
    for m in CHN.finditer(last):
        named[f'Ch {m.group(1)}'].add(name)
    m = OTHER.match(last)
    if m:
        named[f'Ch {m.group(2)}'].add(name)

def fmt(names):
    return ', '.join(f'`{n}`' for n in sorted(names))

ids = sorted(set(named) | set(tagged) | set(cites) | set(mods), key=key)
res = [i for i in ids if ORDER.get(i.split(' ')[0], 9) == 0]
L = []
L.append('# Thesis map')
L.append('')
L.append('Traceability from V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of')
L.append('General Relativity* (PhD thesis, Minnesota, 2015) [QuennevilleBelair2015] to the Lean')
L.append('declarations of `Feec`. Lean names carry no thesis numbers after the refactor')
L.append('(`docs/REFACTOR_PLAN.md` §1); this file is the only place where they meet.')
L.append('')
L.append('**Generated** by `scripts/ThesisMap.sh` from declaration names and docstrings; do not edit by')
L.append('hand, rerun after renaming. A declaration is listed under a thesis id when')
L.append('')
L.append('- **named**: its name encodes the id (`prop_4_17`, `prop417_density_gap`, `ch6_corrected`,')
L.append('  `Sol61`; old names only, banned after the refactor);')
L.append('- **tagged**: its docstring has a `Thesis: Prop 4.17 (corrected)` tag (the convention for new')
L.append('  declarations);')
L.append('- **cited**: its docstring cites the id inside `[QuennevilleBelair2015, ...]`.')
L.append('')
L.append('Every backticked name in a list item below is checked by `scripts/MapCheck.sh`')
L.append('(`#check @name` must elaborate).')
L.append('')
n_named = len(set().union(*named.values())) if named else 0
n_all = len(set().union(*named.values(), *tagged.values(), *cites.values()))
L.append(f'Counts at generation: {len(res)} numbered results (Thm/Prop/Cor/Lemma/Remark/Def), '
         f'{len(ids) - len(res)} equations/sections/chapters, {n_all} distinct declarations '
         f'({n_named} with a thesis-numbered name).')
L.append('')
L.append('## Results')
L.append('')
def section(i):
    L.append(f'### {i}')
    L.append('')
    if named[i]:  L.append(f'- named: {fmt(named[i])}')
    if tagged[i]: L.append(f'- tagged: {fmt(tagged[i])}')
    if cites[i]:  L.append(f'- cited: {fmt(cites[i])}')
    if mods[i]: L.append(f'- modules: {", ".join(sorted(mods[i]))}')
    L.append('')
for i in res:
    section(i)
L.append('## Equations, sections and chapters')
L.append('')
for i in ids:
    if i not in res:
        section(i)
open(out, 'w', encoding='utf-8').write('\n'.join(L).rstrip('\n') + '\n')
print(f'{out}: {len(res)} numbered results, {len(ids) - len(res)} other ids, {n_all} declarations')
EOF
rm -f "$DOCS"
