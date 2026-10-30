module

public import FeecCheck.Util
public import FeecCheck.Env

/-!
# Thesis map

`lake exe feec-thesismap [OUT]` regenerates `docs/THESIS_MAP.md` (thesis result ↦ current Lean
declarations); `lake exe feec-thesismap --check` (run by `lake exe feec-gate`) fails if the file is
not up to date. Sources, per declaration of a `Feec.*` module:

* its docstring: every result, equation, section or chapter cited as
  `[QuennevilleBelair2015], Prop 4.17 (corrected), Thm 4.3` (the citation convention of
  `docs/REFACTOR_PLAN.md`; the location runs to the end of the line, or to the next `;`, `[Key]`
  or backtick, and may start on the line after `[QuennevilleBelair2015],`);
* module sources: the same citations anywhere in a module (module docstring, its
  `## References` entry, comments) list the module;
* thesis-numbered names of the pre-refactor snapshot (`docs/migration/old_theorems.tsv`: a last
  component containing `thm_N_M`, `prop_N_M`, `cor_N_M`, `lemma_N_M` or the compact forms
  `prop417`, `thm43`, `chN_`, `Sol61`, `Hyp54`, `Sys56`, `C55`), listed under their current names
  through `docs/migration/map.tsv`.

Rerun after renames: entries follow the declarations as long as the new declarations carry a
`[QuennevilleBelair2015], ...` citation in their docstring.
-/

public section

namespace FeecCheck.ThesisMap

open Lean Re

/-- `\d+\.\d+`. -/
def num : Re := seqs [plus digit, chr '.', plus digit]

/-- `Theorem|Thm|Proposition|Prop|Corollary|Cor|Lemma|Remark|Definition|Def`. -/
def kindWord : Re :=
  lits ["Theorem", "Thm", "Proposition", "Prop", "Corollary", "Cor", "Lemma", "Remark",
    "Definition", "Def"]

def kindOf (w : String) : String :=
  match w.toLower with
  | "thm" | "theorem" => "Thm"
  | "prop" | "proposition" => "Prop"
  | "cor" | "corollary" => "Cor"
  | "lemma" => "Lemma"
  | "remark" => "Remark"
  | _ => "Def"

/-- `[A-Z][A-Za-z\-]*\d{4}[a-z]?`. -/
def key : Re := seqs [upper, .star (.alt alphaAZ (chr '-')), rep 4 digit, opt lowerAZ]

/-- `\[QuennevilleBelair2015\](?![\[(])(?:,\s*)?((?:[^\n;`\[]|\[(?!KEY\]))*)`: group 1 is the
location. -/
def cite : Re :=
  seqs [lit "[QuennevilleBelair2015]", .look true (oneOf ['[', '(']), opt (.seq (chr ',') (.star space)),
    .group 1 (.star (.alt (noneOf ['\n', ';', '`', '['])
      (.seq (chr '[') (.look true (.seq key (chr ']'))))))]

/-- `\b(KIND)s?\.?\s+(NUM(?:\s*(?:–|-|,|and)\s*NUM)*)`. -/
def res : Re :=
  seqs [.wordB, .group 1 kindWord, opt (chr 's'), opt (chr '.'), plus space,
    .group 2 (.seq num (.star (seqs [.star space, lits ["–", "-", ",", "and"], .star space, num])))]

/-- `\((NUM)([a-z](?:–[a-z])?)?\)(?:\s*–\s*\((NUM)\))?`. -/
def eq : Re :=
  seqs [chr '(', .group 1 num, opt (.group 2 (.seq lowerAZ (opt (.seq (chr '–') lowerAZ)))), chr ')',
    opt (seqs [.star space, chr '–', .star space, chr '(', .group 3 num, chr ')'])]

/-- `§\s*(NUM)(?:\s*–\s*(NUM))?`. -/
def sec : Re :=
  seqs [chr '§', .star space, .group 1 num, opt (seqs [.star space, chr '–', .star space, .group 2 num])]

/-- `\bCh\.\s*(\d+)\b`. -/
def ch : Re := seqs [.wordB, lit "Ch.", .star space, .group 1 (plus digit), .wordB]

def numberedWord : Re := lits ["thm", "prop", "cor", "lemma"]

/-- `(?:^|_)(thm|prop|cor|lemma)_(\d+)_(\d+)|(?:^|_)(thm|prop|cor|lemma)(\d)(\d+)(?![\d])`. -/
def namedRe : Re :=
  .alt (seqs [.alt .bos (chr '_'), .group 1 numberedWord, chr '_', .group 2 (plus digit), chr '_',
      .group 3 (plus digit)])
    (seqs [.alt .bos (chr '_'), .group 4 numberedWord, .group 5 digit, .group 6 (plus digit),
      .look true digit])

/-- `(?:^|_)ch(\d+)_`. -/
def chn : Re := seqs [.alt .bos (chr '_'), lit "ch", .group 1 (plus digit), chr '_']

/-- `^(Sol|Hyp|Sys|C)(\d)(\d+)$`. -/
def other : Re :=
  seqs [.bos, .group 1 (lits ["Sol", "Hyp", "Sys", "C"]), .group 2 digit, .group 3 (plus digit),
    .alt .eos (.seq (chr '\n') .eos)]

/-- `\s*(–|-|,|and)\s*`. -/
def sep : Re := seqs [.star space, .group 1 (lits ["–", "-", ",", "and"]), .star space]

/-- `\n {2,}(?=\S)`: an indented continuation line. -/
def contLine : Re := seqs [chr '\n', rep 2 (chr ' '), .star (chr ' '), .look false nonSpace]

/-- The order of a kind of id: numbered results, equations, sections, chapters. -/
def order (k : String) : Nat :=
  match k with
  | "Thm" | "Prop" | "Cor" | "Lemma" | "Remark" | "Def" => 0
  | "Eq" => 1
  | "Sec" => 2
  | "Ch" => 3
  | _ => 9

/-- `'4.16'` ↦ `(4, 16)`. -/
def chap (p : String) : String × Nat :=
  match p.splitOn "." with
  | a :: b :: _ => (a, pyInt b)
  | _ => (p, 0)

/-- `'4.16–4.18'` ↦ `4.16, 4.17, 4.18`; `'4.17 and 4.19'` ↦ both. -/
def expand (kind s : String) : Array String := Id.run do
  let parts := sep.split s [1]
  let mut ids := #[]
  let mut prev : Option String := none
  for h : i in [0:parts.size] do
    let p := parts[i]
    if (num.fullMatch p).isSome then
      match prev with
      | some q =>
        if i ≥ 2 && (parts[i - 1]! == "–" || parts[i - 1]! == "-") then
          let (a0, a1) := chap q
          let (b0, b1) := chap p
          if a0 == b0 then
            for j in [a1 + 1:b1 + 1] do ids := ids.push s!"{kind} {a0}.{j}"
          else ids := ids.push s!"{kind} {p}"
        else ids := ids.push s!"{kind} {p}"
      | none => ids := ids.push s!"{kind} {p}"
      prev := some p
  return ids

/-- The thesis ids cited in a location text. -/
def cited (text : String) : Array String := Id.run do
  let cs := chars text
  let mut ids := #[]
  for m in res.findAll cs do
    ids := ids ++ expand (kindOf (m.group 1)) (m.group 2)
  for m in eq.findAll cs do
    ids := ids.push s!"Eq ({m.group 1})"
    if let some b := m.group? 3 then
      let (a0, a1) := chap (m.group 1)
      let (b0, b1) := chap b
      if a0 == b0 then
        for j in [a1:b1 + 1] do ids := ids.push s!"Eq ({a0}.{j})"
  for m in sec.findAll cs do
    ids := ids.push s!"Sec §{m.group 1}"
    if let some b := m.group? 2 then
      let (a0, a1) := chap (m.group 1)
      let (b0, b1) := chap b
      if a0 == b0 then
        for j in [a1:b1 + 1] do ids := ids.push s!"Sec §{a0}.{j}"
  for m in ch.findAll cs do
    ids := ids.push s!"Ch {m.group 1}"
  return ids

/-- The sort key of an id, `(order, numbers, kind, rest)`. -/
def sortKey (i : String) : Nat × List Nat × String × String :=
  match i.splitOn " " with
  | k :: rest =>
    let n := " ".intercalate rest
    (order k, ((plus digit).findAll (chars n)).toList.map (fun m => pyInt (m.group 0)), k, n)
  | [] => (9, [], i, "")

def keyLt (a b : String) : Bool :=
  let (a1, a2, a3, a4) := sortKey a
  let (b1, b2, b3, b4) := sortKey b
  if a1 != b1 then a1 < b1
  else if a2 != b2 then decide (a2 < b2)
  else if a3 != b3 then a3 < b3
  else a4 < b4

/-- The docstrings of the `Feec` declarations, as `(name, module, docstring on one line)`
(names and modules printed by `Name.toString`, so escaped as in Lean source). -/
def docRows (env : Environment) : IO (Array (String × String × String)) := do
  let oneLine (s : String) : String :=
    let s := s.map fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c
    " ".intercalate ((s.splitOn " ").filter (· ≠ ""))
  let mut rows := #[]
  for (nm, mod, _) in feecConstants env do
    if nm.isInternal then continue
    let some doc ← findDocString? env nm | continue
    rows := rows.push (toString nm, toString mod, oneLine doc)
  return rows

def fmt (names : Array String) : String := ", ".intercalate (names.toList.map (s!"`{·}`"))

/-- Generate the text of `docs/THESIS_MAP.md`; also returns the summary line. -/
def generate (docs : Array (String × String × String)) : IO (String × String) := do
  let mut named : SetMap := {}
  let mut cites : SetMap := {}
  let mut mods : SetMap := {}
  for (name, mod, doc) in docs do
    for c in cite.findAllGroup (chars doc) do
      for i in cited c do
        cites := cites.add i name
        mods := mods.add i mod
  for f in ← leanFiles "Feec" do
    let mod := moduleOfPath f
    let src ← contLine.sub (m := Id) (chars (← readText f)) fun _ => " "
    for c in cite.findAllGroup src do
      for i in cited c do
        mods := mods.add i mod
  let mut newnames : Std.HashMap String (Std.HashSet String) := {}
  for (line, k) in (pyLines (← readText "docs/migration/map.tsv")).zipIdx do
    let f := line.splitOn "\t"
    if k > 0 && f.length == 3 && f[2]! != "deleted-helper" then
      newnames := newnames.insert f[0]! ((newnames.getD f[0]! {}).insert f[1]!)
  let mut oldnamed : SetMap := {}
  for line in pyLines (← readText "docs/migration/old_theorems.tsv") do
    let name := (line.splitOn "\t").head!
    let last := (name.splitOn ".").getLast!
    let nn := newnames.getD name {}
    let lastCs := chars last
    for m in namedRe.findAll lastCs do
      let i := if (m.group? 1).isSome then s!"{kindOf (m.group 1)} {m.group 2}.{m.group 3}"
        else s!"{kindOf (m.group 4)} {m.group 5}.{m.group 6}"
      oldnamed := oldnamed.add i name
      named := named.addAll i nn
    for m in chn.findAll lastCs do
      let i := s!"Ch {m.group 1}"
      oldnamed := oldnamed.add i name
      named := named.addAll i nn
    if let some m := other.matchAt lastCs 0 then
      let i := s!"Ch {m.group 2}"
      oldnamed := oldnamed.add i name
      named := named.addAll i nn
  let mut all : Std.HashSet String := {}
  for m in [named, oldnamed, cites, mods] do
    for i in m.keys.arr do all := all.insert i
  let ids := all.toArray.qsort keyLt
  let resIds := ids.filter fun i => order ((i.splitOn " ").head!) == 0
  let nNamed := named.union.size
  let nAll := (named.union.fold (fun s x => s.insert x) cites.union).size
  let mut L : Array String := #[
    "# Thesis map",
    "",
    "Traceability from V. Quenneville-Bélair, *A New Approach to Finite Element Simulations of",
    "General Relativity* (PhD thesis, Minnesota, 2015) [QuennevilleBelair2015] to the Lean",
    "declarations of `Feec`. Lean names carry no thesis numbers after the refactor",
    "(`docs/REFACTOR_PLAN.md` §1); this file is the only place where they meet.",
    "",
    "**Generated** by `lake exe feec-thesismap` from declaration names and docstrings; do not edit",
    "by hand, rerun after renaming (`lake exe feec-gate` fails while this file is out of date). A",
    "declaration is listed under a thesis id when",
    "",
    "- **named**: it is a current home (`docs/migration/map.tsv`) of a pre-refactor declaration whose",
    "  name encoded the id (`prop_4_17`, `prop417_density_gap`, `ch6_corrected`, `Sol61`); those old",
    "  names are listed, unchecked, under **old**;",
    "- **cited**: its docstring cites the id, as `[QuennevilleBelair2015], Prop. 4.17 (corrected)`",
    "  (the citation convention of `docs/REFACTOR_PLAN.md`);",
    "- **modules**: the module cites the id anywhere in its source (module docstring,",
    "  `## References`, comments).",
    "",
    "Every backticked name in a list item below is checked by `lake exe feec-mapcheck`",
    "(the declaration must exist).",
    "",
    s!"Counts at generation: {resIds.size} numbered results (Thm/Prop/Cor/Lemma/Remark/Def), \
      {ids.size - resIds.size} equations/sections/chapters, {nAll} distinct declarations \
      ({nNamed} current homes of thesis-numbered old names).",
    "",
    "## Results",
    ""]
  let sect (L : Array String) (i : String) : Array String := Id.run do
    let mut L := L.push s!"### {i}" |>.push ""
    if !(named.get i).isEmpty then L := L.push s!"- named: {fmt (named.sorted i)}"
    if !(oldnamed.get i).isEmpty then L := L.push s!"- old: {", ".intercalate (oldnamed.sorted i).toList}"
    if !(cites.get i).isEmpty then L := L.push s!"- cited: {fmt (cites.sorted i)}"
    if !(mods.get i).isEmpty then L := L.push s!"- modules: {", ".intercalate (mods.sorted i).toList}"
    return L.push ""
  for i in resIds do L := sect L i
  L := L.push "## Equations, sections and chapters" |>.push ""
  for i in ids do
    if !resIds.contains i then L := sect L i
  let text := String.ofList (("\n".intercalate L.toList).toList.reverse.dropWhile (· == '\n')).reverse
  return (text ++ "\n", s!"{resIds.size} numbered results, {ids.size - resIds.size} other ids, \
    {nAll} declarations")

/-- Regenerate (`check = false`: write `out`) or check (`check = true`: compare with `out`). -/
def run (env : Environment) (out : String := "docs/THESIS_MAP.md") (check : Bool := false) :
    IO Report := do
  let (text, summary) ← generate (← docRows env)
  let rep : Report := { name := "ThesisMap" }
  if check then
    let cur ← if ← System.FilePath.pathExists out then readText out else pure ""
    if cur == text then return rep.addInfo s!"{out}: up to date ({summary})"
    let a := pyLines cur
    let b := pyLines text
    let mut n := 0
    while n < a.size && n < b.size && a[n]! == b[n]! do n := n + 1
    return rep.addError s!"{out}:{n + 1}: out of date (first difference at this line); \
      run `lake exe feec-thesismap`"
  IO.FS.writeFile out text
  return rep.addInfo s!"{out}: {summary}"

end FeecCheck.ThesisMap
