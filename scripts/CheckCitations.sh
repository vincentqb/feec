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
# 3. every module docstring has a `## References` section.
#
# Exit status: nonzero if any check fails; each failure is printed as `path:line: message`.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'EOF'
import pathlib, re, sys
bib = set(re.findall(r'@\w+\{([^,\s]+),', pathlib.Path('docs/references.bib').read_text(encoding='utf-8')))
KEY = r'[A-Z][A-Za-z\-]*\d{4}[a-z]?'
CITE = re.compile(r'\[(' + KEY + r')\](?!\()')
INSIDE = re.compile(r'\[(' + KEY + r'),')
errors = []
files = sorted(pathlib.Path('Feec').rglob('*.lean'))
for f in files:
    src = f.read_text(encoding='utf-8')
    for m in CITE.finditer(src):
        if m.group(1) not in bib:
            ln = src.count('\n', 0, m.start()) + 1
            errors.append(f'{f}:{ln}: citation key [{m.group(1)}] has no entry in docs/references.bib')
    for m in INSIDE.finditer(src):
        ln = src.count('\n', 0, m.start()) + 1
        errors.append(f'{f}:{ln}: location inside the brackets ([{m.group(1)}, ...]); '
                      f'write [{m.group(1)}], ...')
    i = src.find('/-!')
    j = src.find('-/', i) if i >= 0 else -1
    if i < 0 or '## References' not in src[i:j]:
        errors.append(f'{f}:1: module docstring has no `## References` section')
for e in errors:
    print(e)
print(f'CheckCitations: {len(files)} files, {len(bib)} bib entries, {len(errors)} errors')
sys.exit(1 if errors else 0)
EOF
