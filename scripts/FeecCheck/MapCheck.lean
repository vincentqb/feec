import FeecCheck.Util
import FeecCheck.Env
import FeecCheck.ThesisMap

/-!
# Migration coverage gate

`lake exe feec-mapcheck [--strict] [--no-env]` (`lake exe feec-gate` runs it with `--strict`;
`docs/REFACTOR_PLAN.md` §5, item 4).

1. Validates `docs/migration/map.tsv` (header `old<TAB>new<TAB>kind`; names fully qualified, e.g.
   `Feec.Constraints.prop_4_17` or `LinearPMap.IsSkewAdjoint`; `new` is `-` for
   `deleted-helper`; kind ∈ rename, generalize, corollary, dedup, counterexample,
   deleted-helper).
2. Every `new` name of `map.tsv` and every backticked name in a `- named:`/`- cited:` item of
   `docs/THESIS_MAP.md` must be a declaration of the environment of `Feec` (what `#check @name`
   accepts: the exact name, or a name that resolves to a declaration from the root namespace,
   such as an `export` alias). `--no-env` skips this step (no import of `Feec`).
3. Reports coverage: rows of `docs/migration/old_theorems.tsv` whose name appears as `old` in
   `map.tsv`; `main` rows may not be `deleted-helper`.
4. Every thesis result cited under `Feec/` as `[QuennevilleBelair2015], Prop 4.17` (the citation
   convention; the location may start on the next line) must have a section in `THESIS_MAP.md`.

Fails on a missing declaration, a malformed row, a `main` row mapped to `deleted-helper`, or a
thesis citation missing from `THESIS_MAP.md`. With `--strict`, also while some row of
`old_theorems.tsv` is not covered by `map.tsv` (the end-of-migration gate).
-/

namespace FeecCheck.MapCheck

open Lean Re

def kinds : List String :=
  ["rename", "generalize", "corollary", "dedup", "counterexample", "deleted-helper"]

/-- `a.b.c` ↦ the name with components `a`, `b`, `c` (as `#check @«a».«b».«c»`). -/
def nameOfString (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => .str n c) .anonymous

/-- Whether `#check @«n»` would elaborate. -/
def exists? (env : Environment) (n : Name) : Bool :=
  env.contains n ||
    (ResolveName.resolveGlobalName env {} .anonymous [] n).any fun (d, fs) => fs.isEmpty && env.contains d

/-- `\b(KIND)s?\.?\s+(\d+\.\d+)`. -/
def resSimple : Re :=
  seqs [.wordB, .group 1 ThesisMap.kindWord, opt (chr 's'), opt (chr '.'), plus space,
    .group 2 ThesisMap.num]

def run (env? : Option Environment) (strict : Bool) : IO Report := do
  let mut rep : Report := { name := "MapCheck" ++ if strict then " (strict)" else "" }
  let mapPath := "docs/migration/map.tsv"
  let tmPath := "docs/THESIS_MAP.md"
  let mapLines := pyLines (← readText mapPath)
  let tmLines := pyLines (← readText tmPath)
  -- 2. names
  if let some env := env? then
    let mut seen : Std.HashSet String := {}
    let mut names : Array (String × String) := #[]
    for (line, k) in mapLines.zipIdx do
      let f := line.splitOn "\t"
      if k > 0 && f.length == 3 && f[1]! != "" && f[1]! != "-" && !seen.contains f[1]! then
        seen := seen.insert f[1]!
        names := names.push (f[1]!, s!"{mapPath}:{k + 1}")
    let backticked := seqs [chr '`', .group 1 (plus (noneOf ['`'])), chr '`']
    for (line, k) in tmLines.zipIdx do
      if line.startsWith "- named:" || line.startsWith "- cited:" then
        for n in backticked.findAllGroup (chars line) do
          unless seen.contains n do
            seen := seen.insert n
            names := names.push (n, s!"{tmPath}:{k + 1}")
    let mut nfail := 0
    for (n, loc) in names do
      unless exists? env (nameOfString n) do
        nfail := nfail + 1
        rep := rep.addError s!"{loc}: `{n}` is not a declaration of Feec"
    rep := rep.addInfo s!"names checked: {names.size} ({nfail} missing)"
  -- 3. coverage
  let mut old : Std.HashMap String Bool := {}
  let mut oldOrder : Array String := #[]
  for line in pyLines (← readText "docs/migration/old_theorems.tsv") do
    let f := line.splitOn "\t"
    unless old.contains f[0]! do oldOrder := oldOrder.push f[0]!
    old := old.insert f[0]! (f.length > 2 && f[2]! == "main")
  if mapLines[0]?.map (·.splitOn "\t") != some ["old", "new", "kind"] then
    rep := rep.addError s!"{mapPath}:1: bad header \
      {pyReprList ((mapLines[0]?.getD "").splitOn "\t")}"
  let mut mapped : Std.HashMap String (Std.HashSet String) := {}
  let mut mappedOrder : Array String := #[]
  let mut notes := 0
  for (line, k0) in (mapLines.extract 1 mapLines.size).zipIdx do
    let k := k0 + 2
    let f := line.splitOn "\t"
    let [o, n, kind] := f | do
      rep := rep.addError s!"{mapPath}:{k}: expected 3 columns, got {f.length}: {pyReprList f}"
      continue
    if !kinds.contains kind then
      rep := rep.addError s!"{mapPath}:{k}: unknown kind {pyRepr kind}"
    if kind == "deleted-helper" && n != "" && n != "-" then
      rep := rep.addError s!"{mapPath}:{k}: deleted-helper must have new = -"
    if kind != "deleted-helper" && (n == "" || n == "-") then
      rep := rep.addError s!"{mapPath}:{k}: {kind} needs a new name"
    if !old.contains o then
      notes := notes + 1
      rep := rep.addInfo s!"  note: {mapPath}:{k}: old name {o} is not in old_theorems.tsv"
    unless mapped.contains o do mappedOrder := mappedOrder.push o
    mapped := mapped.insert o ((mapped.getD o {}).insert kind)
  for o in mappedOrder do
    if old.getD o false && (mapped.getD o {}).contains "deleted-helper" then
      rep := rep.addError s!"{mapPath}: main declaration {o} mapped to deleted-helper"
  let tot := oldOrder.size
  let cov := (oldOrder.filter mapped.contains).size
  let mtot := (oldOrder.filter (old.getD · false)).size
  let mcov := (oldOrder.filter fun o => old.getD o false && mapped.contains o).size
  rep := rep.addInfo s!"coverage: {cov}/{tot} old declarations mapped ({tot - cov} missing); \
    main {mcov}/{mtot}; map.tsv rows {mapLines.size - 1}"
  if strict && cov < tot then
    for o in oldOrder do
      unless mapped.contains o do
        rep := rep.addError s!"docs/migration/old_theorems.tsv: {o} has no row in {mapPath}"
  -- 4. thesis citations
  let heads : Std.HashSet String := tmLines.foldl (init := {}) fun s l =>
    if l.startsWith "### " && l.length > 4 then s.insert (l.drop 4).toString else s
  let mut ncite := 0
  for p in ← leanFiles "Feec" do
    let src := chars (← readText p)
    for c in ThesisMap.cite.findAll src do
      for m in resSimple.findAll (chars (c.group 1)) do
        ncite := ncite + 1
        let i := s!"{ThesisMap.kindOf (m.group 1)} {m.group 2}"
        unless heads.contains i do
          rep := rep.addError s!"{p}:{lineOf src c.start}: thesis citation {i} has no section \
            in THESIS_MAP.md"
  return rep.addInfo s!"thesis citations checked: {ncite}"

end FeecCheck.MapCheck
