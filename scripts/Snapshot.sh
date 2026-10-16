#!/usr/bin/env bash
# Snapshot every declaration of the Feec library (run once at the pre-migration HEAD).
#
#   scripts/Snapshot.sh [OUT]          (default OUT = docs/migration/old_theorems.tsv)
#
# Requires an up-to-date `lake build Feec`. Writes OUT with columns
#   name <TAB> type <TAB> main <TAB> kind
# where `main` is the literal `main` for the "main" set and empty otherwise:
#   * thesis-numbered names: a last component containing thm_N / prop_N / cor_N / lemma_N
#     (underscore optional, e.g. prop417_density_gap) /
#     chN_ (e.g. prop_4_17, thm_4_6_strong, mirror_prop_4_17_exists, ch6_corrected), or of the
#     form Sol61 / Hyp54 / Sys56 / C55;
#   * names appearing in docs/OVERVIEW.md inside backticks (full name, name without the
#     `Feec.` root, or a component-aligned suffix of at least 3 characters).
# `kind` is theorem / def / opaque / axiom / inductive.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT="${1:-docs/migration/old_theorems.tsv}"
RAW="$(mktemp /tmp/feec_snapshot_raw.XXXXXX.tsv)"
FEEC_SNAPSHOT_OUT="$RAW" lake env lean scripts/Snapshot.lean
python3 - "$RAW" "$OUT" docs/OVERVIEW.md <<'EOF'
import re, sys
raw, out, overview = sys.argv[1:4]
num = re.compile(r'(^|_)(thm|prop|cor|lemma)_?\d|(^|_)ch\d+_|^(Sol|Hyp|Sys|C)\d{2,3}$')
ident = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?₀-₉ᵢ]*")
toks = set()
for span in re.findall(r'`([^`\n]+)`', open(overview, encoding='utf-8').read()):
    for t in ident.findall(span):
        t = t.strip('.')
        if t.startswith('Feec.'):
            t = t[5:]
        if len(t) >= 3 and re.search('[A-Za-z]', t):
            toks.add(t)
def is_main(name):
    comps = name.split('.')
    if num.search(comps[-1]):
        return True
    for k in range(1, len(comps) + 1):
        if '.'.join(comps[-k:]) in toks:
            return True
    return False
n = m = 0
with open(raw, encoding='utf-8') as f, open(out, 'w', encoding='utf-8') as g:
    for line in f:
        line = line.rstrip('\n')
        if not line:
            continue
        name, ty, kind = line.split('\t')
        main = 'main' if is_main(name) else ''
        n += 1; m += bool(main)
        g.write(f'{name}\t{ty}\t{main}\t{kind}\n')
print(f'{out}: {n} declarations, {m} main')
EOF
rm -f "$RAW"
