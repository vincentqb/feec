module

public import FeecCheck.Util
public import FeecCheck.Env
public import FeecCheck.Citations

/-!
# Doc-name gate

`lake exe feec-docnames` (also run by `lake exe feec-gate`) checks that the Lean names the
documentation mentions exist: every inline code span (`` `…` ``) of `README.md` and `docs/*.md`
that looks like a Lean name must resolve, in the environment of `Feec` and `FeecCheck`, to a
declaration, a module, a namespace, an option or a token (a tactic name such as `fin_cases`).

**What counts as a name.** Fenced code blocks are skipped. A span is a name candidate when, after
dropping a leading `@`, it has no whitespace (spaces after the commas of a brace group are
removed first) and every `.`-separated atom is a Lean identifier atom, and moreover

* it has at least two atoms and the first starts with an upper-case letter and has at least two
  characters (`Feec.Models.Cube.Sobolev`, `LinearPMap.closedRange_tfae`; dot notation on a
  variable such as `c.symm` is not a name), or
* it is one atom with at least two `_`-separated pieces of length `≥ 2` (`exact_mid`, but not the
  subscripts `S_h`, `G_ab`), or one camelCase atom (`ofGalerkinCore`, `ReducingSubcomplex`).

Math notation (`D(d) ∩ D(d†)`, `P_rΛᵏ`, `h^{1/2}`), file names (`map.tsv`, `Design.lean`), paths
(`Feec/Ch4/Adjoint.lean`), globs (`prop_*`, `thm_[0-9]`) and single lower-case words (`trunc`)
are not candidates.

**Shorthands.** Groups are expanded: `P.{a, b}` is `P.a` and `P.b`, `bggComplex_{eq61, of_eq61}`
and `HasCompactEmbedding{,0,2}` likewise, an optional part `mixed_rate_polyTr(_of_polyOrderAt)`
gives the name with and without it, and `gradCurl_coreSub_spectral_Q/_cube` replaces the last
`_`-piece. A span `_rate` or `_rate_sobolev` that follows a name span, separated only by
punctuation and the words `and`, `or`, `with`, is a suffix of that name: it must resolve as
the name, or the name cut at one of its `_`, followed by the suffix
(`FEM.einsteinBianchi_mirrorFEM_ofComplexCrime`, `_rate`, `_rate_sobolev`); likewise `.x` after
a name is a field of it (`Feec.ForcingDLOrW11` (with `.admissible`)). Elsewhere such a span names
a suffix (`_unconditional` in the naming rules) and is not checked. A glob `P.*` checks `P`.

**Resolution.** A name resolves if it is a declaration, module, namespace or a `.`-prefix of a
module, or if its atoms are the last atoms of one (`Cube.TangentialRate` for
`Feec.Models.Cube.TangentialRate`, `IsCsFormTr.d_eq` for `Feec.….IsCsFormTr.d_eq`).

**Historical sections.** The documents keep records of the refactor: the pre-refactor tree,
the dated status notes (block quotes starting with `**Status (YYYY-MM-DD)`), the description of
the old names in the header of `docs/THESIS_MAP.md`. They name declarations as they were at the
time. In these regions (`historical` in `regions`) a name also resolves against the declarations
of the pre-refactor tree (`docs/migration/old_theorems.tsv`, the `old` column of
`docs/migration/map.tsv`), and the few names that existed only between the refactor and a later
deletion or renaming are listed in `historicalNames` (an entry also covers the names below it).

**Proposals.** The pre-refactor blueprint (`docs/BLUEPRINT.md`, its review) and the parts of
`docs/REFACTOR_PLAN.md` written before the refactor as a proposal (§0, §2–§4: decisions, core
abstractions, planned generalizations, migration map) name declarations that were planned, many
under other names in the end; their names are not checked (`proposal` in `regions`). The plan's
§1 (import and naming rules), §5 (the gate) and §6, and the rest of the documents, are checked.

**Banned examples.** The examples of banned identifiers in the naming rules of
`docs/REFACTOR_PLAN.md` §1 (`banned` in `regions`) must *not* resolve.

An entry of `regions` or `historicalNames` that matches nothing is an error, so both lists stay
minimal. Citation keys of `docs/references.bib` (`AFW2010`) also resolve.

Violations are reported as `path:line: message` at the line where the span starts.
-/

public section

namespace FeecCheck.DocNames

open Lean

/-- How the names of a region are checked. -/
inductive Kind where
  /-- Current names only. -/
  | current
  /-- Current names, old declarations and `historicalNames`. -/
  | historical
  /-- Examples of banned names: they must *not* resolve. -/
  | banned
  /-- Not checked. -/
  | proposal
  deriving BEq, Inhabited

def Kind.rank : Kind → Nat
  | .current => 0
  | .historical => 1
  | .banned => 2
  | .proposal => 3

def Kind.max (a b : Kind) : Kind := if a.rank ≥ b.rank then a else b

/-- The regions that are not checked as current documentation: `(file, anchor, kind)`. The anchor
`""` is the whole file; an anchor starting with `#` begins a heading line, and the region runs to
the next heading; any other anchor starts a paragraph or list item, which is the region. Dated
status notes are `historical` wherever they are. -/
def regions : List (String × String × Kind) :=
  [ -- the blueprint of the chapter-ordered tree and its review
    ("docs/BLUEPRINT.md", "", .proposal),
    ("docs/BLUEPRINT-REVIEW.md", "", .proposal),
    -- the plan before the refactor: inventory and decisions, the abstractions and generalized
    -- theorems it proposed, and its migration map
    ("docs/REFACTOR_PLAN.md", "# Final refactor plan", .historical),
    ("docs/REFACTOR_PLAN.md", "## 0. Decisions", .proposal),
    ("docs/REFACTOR_PLAN.md", "## 2. Core abstractions", .proposal),
    ("docs/REFACTOR_PLAN.md", "## 3. Generalized theorems", .proposal),
    ("docs/REFACTOR_PLAN.md", "## 4. Migration map", .proposal),
    -- the old tree, as a record
    ("docs/OVERVIEW.md", "## The pre-refactor tree", .historical),
    -- the old names that the thesis map lists under **old**, with examples
    ("docs/THESIS_MAP.md", "- **named**:", .historical),
    -- the examples of banned identifiers of the naming rules
    ("docs/REFACTOR_PLAN.md", "- thesis numbers:", .banned),
    ("docs/REFACTOR_PLAN.md", "- thesis typography:", .banned)]

/-- Names of historical regions that are neither current nor old declarations: the roots of the
pre-refactor tree (modules, not declarations) and the names that existed only between the refactor
and a later renaming or deletion, as the dated status notes record. An entry also covers the names
below it (`Feec.Foundation` covers `Feec.Foundation.Operators`). -/
def historicalNames : List String :=
  [ -- the chapter-ordered tree and the real-scalar layer that remained of it
    "Feec.Ch2", "Feec.Ch7", "Feec.Repair", "Feec.Foundation", "Feec.Legacy",
    -- renamed: the `ThesisEB` structure and the thesis-numbered witnesses of Prop 5.9
    "ThesisEB", "exists_counterexample_prop59_two", "exists_counterexample_prop59_two_bestApprox",
    "not_exists_prop59_two_bound",
    -- deleted by the minimality pass of 2026-10-22 (empty modules, superseded results)
    "ForMathlib.LinearPMap.CompPartial", "Models.BoundedDomain.DeRham", "deRham3",
    "planeWave_unique", "mirror_waveFEM_rate",
    "Feec.Models.BoundedDomain.bggComplex_isStrongSolution_of_weakEqs",
    -- deleted by the static model migration (crown WP6): the rates are those of the static FEEC
    -- theorem for the conforming families of the models
    "Feec.Models.Cube.DeRhamIdentRate"]

/-- File extensions: a dotted span ending in one is a file name, not a Lean name. -/
def fileExts : List String :=
  ["lean", "md", "tsv", "bib", "toml", "json", "txt", "sh", "py", "olean", "tex", "pdf", "log"]

/-! ### Extracting the code spans -/

/-- An inline code span of a document. -/
structure Span where
  line : Nat
  text : String
  /-- The text between the previous span of the paragraph and this one (`none` for the first). -/
  before : Option String
  kind : Kind

/-- A heading line `#… title`: `(level, title)`. -/
def heading? (line : String) : Option (Nat × String) :=
  let n := (line.toList.takeWhile (· == '#')).length
  if n ≥ 1 && n ≤ 6 && (line.drop n).startsWith " " then some (n, pyStrip (line.drop n).toString)
  else none

/-- Whether a line opens or closes a fenced code block. -/
def isFence (line : String) : Bool :=
  let t := pyStrip line
  t.startsWith "```" || t.startsWith "~~~"

/-- A block-quote line: its content after `>` and one space. -/
def quoted? (line : String) : Option String :=
  let t := (line.toList.dropWhile (· == ' '))
  match t with
  | '>' :: ' ' :: r => some (String.ofList r)
  | '>' :: r => some (String.ofList r)
  | _ => none

/-- `**Status (YYYY-MM-DD)` at the start of a block quote: a dated status note. -/
def isStatusNote (content : String) : Bool :=
  let t := pyStrip content
  t.startsWith "**Status (" &&
    let d := (t.toList.drop "**Status (".length).take 10
    d.length == 10 && d.zipIdx.all fun (c, i) => if i == 4 || i == 7 then c == '-' else c.isDigit

/-- The code spans of a paragraph (its lines with their line numbers). -/
def spansOf (lines : Array (Nat × String)) (kind : Kind) : Array Span := Id.run do
  -- the paragraph as one character array, with the line of each character
  let mut cs : Array Char := #[]
  let mut ln : Array Nat := #[]
  for (k, l) in lines do
    for c in l.toList do
      cs := cs.push c
      ln := ln.push k
    cs := cs.push '\n'
    ln := ln.push k
  let mut out := #[]
  let mut i := 0
  let mut lastEnd : Option Nat := none
  while i < cs.size do
    if cs[i]! != '`' then
      i := i + 1
      continue
    let mut n := 0
    while i + n < cs.size && cs[i + n]! == '`' do n := n + 1
    -- find the closing run of exactly `n` backticks
    let mut j := i + n
    let mut close : Option Nat := none
    while j < cs.size do
      if cs[j]! == '`' then
        let mut m := 0
        while j + m < cs.size && cs[j + m]! == '`' do m := m + 1
        if m == n then
          close := some j
          break
        j := j + m
      else j := j + 1
    match close with
    | none => i := i + n
    | some e =>
      let raw := ofChars cs (i + n) e
      let text := pyStrip (raw.replace "\n" " ")
      let before := lastEnd.map fun b => ofChars cs b i
      out := out.push { line := ln[i]!, text, before, kind }
      lastEnd := some (e + n)
      i := e + n
  return out

/-- Whether a line starts a list item (`- `, `* `, `+ `, `1. `). -/
def isItem (line : String) : Bool :=
  let t := (line.toList.dropWhile (· == ' '))
  match t with
  | c :: ' ' :: _ => c == '-' || c == '*' || c == '+'
  | _ =>
    let ds := t.takeWhile Char.isDigit
    !ds.isEmpty && (t.drop ds.length).take 2 == ['.', ' ']

/-- The code spans of a document (fenced blocks skipped), with the kind of their region. -/
def docSpans (file : String) (src : String) : Array Span := Id.run do
  let rs := (regions.filter (·.1 == file)).map (·.2)
  let whole := ((rs.filter (·.1 == "")).map (·.2)).foldl Kind.max .current
  let mut sect := whole
  let mut out := #[]
  let mut para : Array (Nat × String) := #[]
  let mut paraKind := Kind.current
  let mut inFence := false
  let mut quote := false
  let mut status := false
  for (l, k) in (pyLines src).zipIdx do
    let line := k + 1
    if inFence then
      if isFence l then inFence := false
      continue
    let q := quoted? l
    let c := q.getD l
    -- paragraph boundaries: blank lines, headings, fences, list items, entering or leaving a
    -- block quote
    let blank := (pyStrip c).isEmpty
    let flush := blank || isFence l || (heading? l).isSome || q.isSome != quote || isItem c
    if flush && !para.isEmpty then
      out := out ++ spansOf para paraKind
      para := #[]
    if q.isNone then
      quote := false
      status := false
    if isFence l then
      inFence := true
      continue
    if (heading? l).isSome then
      sect := (rs.filter fun r => r.1.startsWith "#" && l.startsWith r.1).foldl
        (fun a r => a.max r.2) whole
      continue
    if blank then continue
    if q.isSome && !quote then
      quote := true
      status := isStatusNote c
    if para.isEmpty then
      let anchored := (rs.filter fun r => !r.1.isEmpty && !r.1.startsWith "#" &&
        (pyStrip c).startsWith r.1).foldl (fun a r => a.max r.2) Kind.current
      paraKind := (sect.max anchored).max (if status then .historical else .current)
    para := para.push (line, c)
  if !para.isEmpty then out := out ++ spansOf para paraKind
  return out

/-! ### Name candidates -/

/-- Split at the first group `{…}` or `(…)` (no nesting): `(prefix, alternatives, rest)`. An
optional group `(…)` also allows the empty alternative. -/
def splitGroup (s : String) : Option (String × List String × String) := do
  let cs := s.toList
  let i ← cs.findIdx? (fun c => c == '{' || c == '(')
  let o := cs[i]!
  let c := if o == '{' then '}' else ')'
  let j ← (cs.drop (i + 1)).findIdx? (· == c)
  let inner := String.ofList ((cs.drop (i + 1)).take j)
  let alts := inner.splitOn ","
  -- `(…)` is an optional suffix only when every alternative starts with `_` or `'`
  -- (`mixed_rate_polyTr(_of_polyOrderAt)`, `prop_4_16(_exists, ')`), not in `HΛ_J(Q)`
  if o == '(' && !alts.all (fun a => a.startsWith "_" || a.startsWith "'") then none
  let alts := if o == '(' then "" :: alts else alts
  return (String.ofList (cs.take i), alts, String.ofList (cs.drop (i + 2 + j)))

/-- All expansions of the groups of a span (at most 64). -/
partial def expand (s : String) (fuel : Nat := 6) : List String :=
  match fuel, splitGroup s with
  | 0, _ => [s]
  | _, none => [s]
  | f + 1, some (p, alts, r) => (alts.flatMap fun a => expand (p ++ a ++ r) f).take 64

/-- `a/_b/_c`: `a`, and `a` with its last `_`-piece replaced by `_b`, by `_c`. `none` for a
path. -/
def expandSlash (s : String) : Option (List String) :=
  match s.splitOn "/" with
  | [a] => some [a]
  | a :: rest =>
    if a.isEmpty || !rest.all (·.startsWith "_") then none
    else
      let base := match a.splitOn "_" with
        | [] | [_] => a
        | ps => "_".intercalate ps.dropLast
      some (a :: rest.map (base ++ ·))
  | [] => none

def isAtom (a : String) : Bool :=
  match a.toList with
  | [] => false
  | c :: cs => (isIdFirst c || c.isDigit) && cs.all isIdRest

def isAsciiLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def isAsciiUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- Whether an atom is camelCase: an ASCII letter first, then a lower-case letter followed by an
upper-case one, and at least four characters. -/
def isCamel (a : String) : Bool :=
  let cs := a.toList
  cs.length ≥ 4 && (cs.head?.map fun c => isAsciiLower c || isAsciiUpper c).getD false &&
    (cs.zip cs.tail).any fun (x, y) => isAsciiLower x && isAsciiUpper y

/-- Whether a string (without groups) looks like a Lean name (see the module docstring). -/
def nameLike (s : String) : Bool :=
  let atoms := s.splitOn "."
  if s.isEmpty || !atoms.all isAtom then false
  else if fileExts.contains atoms.getLast! && atoms.length ≥ 2 then false
  else match atoms with
    | [a] =>
      !a.startsWith "_" &&
        (((a.splitOn "_").filter (·.length ≥ 2)).length ≥ 2 || isCamel a)
    | a :: _ =>
      a.length ≥ 2 && (a.toList.head?.map isAsciiUpper).getD false
    | [] => false

/-- The candidate names of a span, or `none` if it is not a name. -/
def candidates (t : String) : Option (List String) := do
  let t := if t.startsWith "@" then (t.drop 1).toString else t
  -- `Feec.Fourier.*`: the namespace or module prefix itself
  let t := if t.endsWith ".*" then String.ofList (t.toList.dropLast.dropLast) else t
  -- spaces after the commas of a group
  let t := (t.splitOn ", ").foldl (fun acc p => if acc.isEmpty then p else acc ++ "," ++ p) ""
  if t.any isPySpace || t.any (· == '*') || t.any (· == '[') then none
  let cs := (expand t).flatMap fun e => (expandSlash e).getD []
  if cs.isEmpty then none
  let cs := cs.filter nameLike
  if cs.isEmpty then none else some cs

/-- A suffix span: `_x` (continuing the last atom) or `.x` (a field of the name). -/
def suffix? (t : String) : Option String :=
  if (t.startsWith "_" || t.startsWith ".") && t.length ≥ 2 &&
      ((t.drop 1).toString.splitOn ".").all isAtom then some t
  else none

/-- Whether the text between two spans only separates them (punctuation, `and`, `or`, `with`). -/
def isSeparator (s : String) : Bool :=
  (pyWords (s.map fun c => if c == ',' || c == ';' || c == '(' || c == ')' then ' ' else c)).all
    fun w => w == "and" || w == "or" || w == "with"

/-- The names `base ++ suf` and `base` cut at one of the `_` of its last atom, followed by `suf`. -/
def suffixCandidates (base suf : String) : List String :=
  if suf.startsWith "." then [base ++ suf] else
  let pre := match base.splitOn "." with
    | [] => ""
    | ps => String.join (ps.dropLast.map (· ++ "."))
  let last := (base.splitOn ".").getLast!
  let pieces := last.splitOn "_"
  (base ++ suf) :: ((List.range pieces.length).drop 1 |>.map fun k =>
    pre ++ "_".intercalate (pieces.take k) ++ suf)

/-! ### Resolution -/

/-- `a.b.c` ↦ the name with components `a`, `b`, `c`. -/
def nameOfString (s : String) : Name :=
  (s.splitOn ".").foldl (fun n c => .str n c) .anonymous

def atomsOf (n : Name) : List String := n.components.map (·.toString (escape := false))

/-- Names indexed by their last atom, for suffix lookups. -/
structure Index where
  byLast : Std.HashMap String (Array Name) := {}
  all : Std.HashSet Name := {}

namespace Index

def add (ix : Index) (n : Name) : Index :=
  if ix.all.contains n then ix else
    let k := (atomsOf n).getLast?.getD ""
    { byLast := ix.byLast.insert k ((ix.byLast.getD k #[]).push n), all := ix.all.insert n }

/-- Whether `s` is a name of the index or the last atoms of one. -/
def resolves (ix : Index) (s : String) : Bool :=
  let ts := s.splitOn "."
  ix.all.contains (nameOfString s) ||
    (ix.byLast.getD ts.getLast! #[]).any fun n =>
      let as := atomsOf n
      as.length ≥ ts.length && as.drop (as.length - ts.length) == ts

end Index

/-- The index of the environment: declarations, modules and their prefixes, namespaces. -/
def envIndex (env : Environment) : Index := Id.run do
  let mut ix : Index := {}
  for (n, _) in env.constants.map₁.toList do ix := ix.add n
  for (n, _) in env.constants.map₂.toList do ix := ix.add n
  for m in env.header.moduleNames do
    let mut p := m
    while !p.isAnonymous do
      ix := ix.add p
      p := p.getPrefix
  for n in env.getNamespaces do ix := ix.add n
  return ix

/-- The old declarations: `docs/migration/old_theorems.tsv` and the `old` column of `map.tsv`. -/
def oldIndex : IO Index := do
  let mut ix : Index := {}
  for l in pyLines (← readText "docs/migration/old_theorems.tsv") do
    if let some n := (l.splitOn "\t").head? then
      unless n.isEmpty do ix := ix.add (nameOfString n)
  for l in (pyLines (← readText "docs/migration/map.tsv")).drop 1 do
    if let some n := (l.splitOn "\t").head? then
      unless n.isEmpty do ix := ix.add (nameOfString n)
  return ix

/-- The documents: `README.md` and `docs/*.md`, sorted. -/
def docFiles : IO (Array String) := do
  let mut out := #["README.md"]
  let ds ← System.FilePath.readDir "docs"
  let mds := ds.filter (·.path.extension == some "md") |>.map (·.path.toString)
  return out ++ mds.qsort (· < ·)

/-- Whether `s` is `M.d` with `M` the last atoms of a module and `d` the last atoms of a
declaration of that module (`LumerPhillips.existsUnique_normalized_contraction`). -/
def moduleQualified (env : Environment) (ix : Index) (s : String) : Bool :=
  let ts := s.splitOn "."
  (List.range ts.length).drop 1 |>.any fun k =>
    let pre := ts.take k
    let rest := ts.drop k
    (ix.byLast.getD ts.getLast! #[]).any fun n =>
      let as := atomsOf n
      as.length ≥ rest.length && as.drop (as.length - rest.length) == rest &&
        match moduleOf? env n with
        | some m =>
          let ms := atomsOf m
          ms.length ≥ pre.length && ms.drop (ms.length - pre.length) == pre
        | none => false

/-- Whether `n` is an entry of `historicalNames` or below one. -/
def historicalEntry? (n : String) : Option String :=
  historicalNames.find? fun h => n == h || n.startsWith (h ++ ".")

def run (env : Environment) : IO Report := do
  let mut rep : Report := { name := "DocNames" }
  let ix := envIndex env
  let old ← oldIndex
  let opts ← getOptionDecls
  let toks := Parser.getTokenTable env
  let bib ← match ← Citations.readBib with
    | .ok b => pure b
    | .error e => do
      rep := rep.addError e
      pure {}
  let current (s : String) : Bool :=
    ix.resolves s || moduleQualified env ix s || opts.contains (nameOfString s) ||
      (toks.find? s).isSome || bib.contains s
  let mut usedNames : Std.HashSet String := {}
  let mut nspans := 0
  let mut nnames := 0
  let mut nold := 0
  let mut nprop := 0
  for file in ← docFiles do
    let spans := docSpans file (← readText file)
    nspans := nspans + spans.size
    -- the base name of the previous span, for suffix shorthands
    let mut base : Option String := none
    for sp in spans do
      let prevBase := if (sp.before.map isSeparator).getD false then base else none
      let cands? : Option (List String) := match suffix? sp.text, prevBase with
        | some suf, some b => some (suffixCandidates b suf)
        | some _, none => none
        | none, _ => candidates sp.text
      -- a suffix keeps the base of its chain (`_rate`, `_rate_sobolev`); a name is a new base
      match suffix? sp.text with
      | some _ => base := prevBase
      | none => base := (candidates sp.text).bind (·.head?)
      let some cands := cands? | continue
      -- a group expands to several names, each must resolve; a suffix shorthand to alternatives,
      -- one must resolve
      let groups : List (List String) :=
        if (suffix? sp.text).isSome then [cands] else cands.map ([·])
      for g in groups do
        if sp.kind == .proposal then
          nprop := nprop + 1
          continue
        nnames := nnames + 1
        if sp.kind == .banned then
          if let some n := g.find? current then
            rep := rep.addError s!"{file}:{sp.line}: `{sp.text}`: {n} is given as an example of a \
              banned name, but it resolves to a declaration"
          continue
        if g.any current then continue
        if sp.kind == .historical then
          if g.any old.resolves then
            nold := nold + 1
            continue
          if let some h := g.findSome? historicalEntry? then
            usedNames := usedNames.insert h
            continue
        let what := if g.length == 1 then g.head! else s!"any of {g}"
        rep := rep.addError s!"{file}:{sp.line}: `{sp.text}`: {what} is not a declaration, \
          module or namespace{if sp.kind == .historical then " (nor an old declaration)" else ""}"
  for (f, a, _) in regions do
    let present ← if a.isEmpty then System.FilePath.pathExists f
      else do
        let ls := pyLines (← readText f)
        pure (if a.startsWith "#" then ls.any (·.startsWith a)
          else ls.any fun l => (pyStrip ((quoted? l).getD l)).startsWith a)
    unless present do
      rep := rep.addError s!"scripts/FeecCheck/DocNames.lean:1: regions: {f} has no \
        {if a.startsWith "#" then "heading" else "paragraph"} {pyRepr a}; update the list"
  for n in historicalNames do
    unless usedNames.contains n do
      rep := rep.addError s!"scripts/FeecCheck/DocNames.lean:1: historicalNames: {n} is not \
        needed any more; remove it"
  return rep.addInfo s!"docnames: {nspans} code spans in {(← docFiles).size} documents, \
    {nnames} names checked ({nold} old names in historical regions), {nprop} names of \
    proposals not checked"

end FeecCheck.DocNames
