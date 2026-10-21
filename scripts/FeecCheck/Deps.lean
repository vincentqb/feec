import FeecCheck.Util
import FeecCheck.Env
import FeecCheck.Snapshot
import FeecCheck.Citations
import FeecCheck.MapCheck

/-!
# Dependency analysis of `Feec` (minimality)

`lake exe feec-deps [--core-docs] [--moddoc] [OUT_DIR]` (default `.lake/feec-deps`) analyses the
environment of `Feec` and writes TSV reports to `OUT_DIR`. It is a measurement tool for the
minimality pass, not a gate check: it never fails on the content of the library.

**Source groups.** The unit of deletion is a *source group*: the text range of one command. Each
constant of a `Feec.*` module with a declaration range of its own opens a range; ranges nested in
another range of the same module (structure fields, constructors, `where` helpers, `@[simps]`
lemmas) join the outer group; a constant without a range of its own (`_proof_i`, `match_i`,
equation lemmas, recursors, `noConfusion`, …) joins the group of its nearest name prefix that has
one. Deleting a group deletes all its members at once, so liveness is decided per group.

**KEEP.** The seeds are
1. the `new` names of `docs/migration/map.tsv` whose `old` name is `main` in
   `docs/migration/old_theorems.tsv`;
2. every declaration named in a backticked span of `README.md`, `docs/OVERVIEW.md`,
   `docs/THESIS_MAP.md`, `docs/THESIS_REFERENCES.md` and the other `docs/*.md` (with
   `--core-docs`, only the first four files): a
   token resolves to every constant whose name ends with it component-wise (dropping leading
   components of a dotted token until something matches, so `F.Verdict` finds `Verdict`); `_sfx`
   tokens extend the previous token of the line, and `…PMC…` tokens also stand for `…PEC…`;
3. with `--moddoc`, every declaration named in a module or section docstring (`/-! … -/`) of a
   `Feec` module (resolved in that module first, then anywhere); without it, such dead groups
   are only flagged (`modDoc` column of `dead.tsv`: deleting one means editing that docstring);
4. every declaration whose docstring cites a work (`[Key]` with `Key` in `docs/references.bib`);
5. metaprograms (syntax, macros, elaborators, delaborators: a type in `Lean.*`, `Mathlib.*`,
   `Aesop.*`, `Qq.*`) and coercion instances (`Coe*` classes: the elaborator unfolds them, so
   they leave no trace in terms).

KEEP is the closure of the seeds under "uses" (constants of the types **and** values of every
member of a kept group), followed by protection rounds until nothing changes: a group outside the
closure is kept anyway if it contains an instance (elaboration may use an instance without
leaving a trace in the term) or if its name (last component) occurs in code (comments, docstrings
and strings blanked) outside the groups still outside the closure: `simp only [rfl_lemma]`,
`change`, `show`, `unfold`, simp arguments that do not fire, `attribute [simp] x` leave no trace in
terms. **DEAD** is every other group; deleting all dead groups never breaks a kept term and leaves
no dangling name in code. The `textrefs` column of `dead.tsv` still counts occurrences in
comments and docstrings (to update after a deletion), and `rflSimp` flags `@[simp]` lemmas proved
by `rfl`. A deletion is checked by building.

**Reports** (`OUT_DIR/*.tsv`, `summary.md`): `dead.tsv` (dead groups: deletion range `line`–
`endLine`, size, text references, the `map.tsv` rows they are `new` of, the dead groups using
them and their modules), `dead_by_module.tsv`, `keep_seeds.tsv`, `dups.tsv`
(theorems with the same statement up to universe levels and binder names, definitions with the
same type and value), `wrappers.tsv` (declarations whose value is a single application of another
constant: every constant of the value but one, `c`, already occurs in the type, or is glue such as
`Iff.mp`, `Eq.symm`; with the modules using them), `largest.tsv` (theorems and definitions by
source lines and by term size), `twins.tsv` (kept proofs of at least 20 lines with the same last
name component in different namespaces: copies to generalize and merge), `map_dead.tsv` (rows
of `map.tsv` whose `new` declaration is dead, with the action that keeps the migration gate
green), `doc_tokens.tsv` (how the doc tokens resolved), `orphans.tsv`.

`lake exe feec-deps --strip FILE OUT [DIR]` writes `FILE` without its dead groups (the ranges of
`DIR/dead.tsv`, default `.lake/feec-deps`) to `OUT`. The deletion range of a group extends its
declaration range (docstring and attributes included) upwards over command prefixes
(`omit … in`, `variable … in`, `open … in`, `set_option … in`) that apply to it alone.

The analysis was validated by compiling stripped copies of eleven modules from nine directories
(437 dead groups, about 3950 lines) against the built library with the options of
`lakefile.toml` (`lake env lean -DmaxSynthPendingDepth=3 …`): no error, no warning.
-/

namespace FeecCheck.Deps

open Lean Meta

/-- `(line, column)` of a position, for lexicographic comparison. -/
def posKey (p : Position) : Nat × Nat := (p.line, p.column)

def leKey (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- The directory of a module: `Feec.Models.Cube.Foo` ↦ `Feec/Models/Cube`. -/
def dirOf (mod : Name) : String :=
  "/".intercalate (mod.components.dropLast.map (·.toString (escape := false)))

def nameStr (n : Name) : String := n.toString (escape := false)

/-- The last component of the user-facing name. -/
def lastComp (n : Name) : String :=
  match privateToUserName n with
  | .str _ s => s
  | .num p _ => match p with | .str _ s => s | _ => ""
  | _ => ""

def kindStr : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

/-- Glue constants allowed around the single application of a wrapper. -/
def glue : List Name :=
  [``Iff.mp, ``Iff.mpr, ``Iff.symm, ``Eq.symm, ``Eq.mp, ``Eq.mpr, ``id, ``And.left, ``And.right,
    ``Iff.rfl, ``Eq.refl, ``rfl, ``Ne.symm, `le_of_eq, `ge_of_eq, ``HEq.refl, ``Iff.refl,
    ``Function.comp, `Eq.le, `Eq.ge]

def coeClasses : List Name :=
  [``Coe, ``CoeTail, ``CoeHead, ``CoeOut, ``CoeDep, ``CoeFun, ``CoeSort, ``CoeT, ``CoeTC,
    ``CoeOTC, ``CoeHTC, ``CoeHTCT]

def metaRoots : List String := ["Lean", "Mathlib", "Aesop", "Qq", "Batteries"]

/-- Strip leading `fun` binders and metadata. -/
partial def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | .mdata _ e => stripLams e
  | e => e

def isRflProof (v : Expr) : Bool :=
  match (stripLams v).getAppFn.constName? with
  | some c => [``Eq.refl, ``rfl, ``Iff.rfl, ``Iff.refl, ``HEq.refl, ``HEq.rfl].contains c
  | none => false

/-- Identifier tokens (possibly dotted) of a string. -/
def idTokens (s : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur : List Char := []
  for c in s.toList ++ [' '] do
    if isIdRest c || c == '.' then cur := c :: cur
    else
      if !cur.isEmpty then
        let t := cur.reverse.dropWhile (· == '.') |>.reverse.dropWhile (· == '.') |>.reverse
        if let some c0 := t.head? then
          if isIdFirst c0 && !c0.isDigit then out := out.push (String.ofList t)
        cur := []
  return out

/-- Backticked spans of a markdown text (outside fenced code blocks), with their 1-based lines. -/
def backtickSpans (text : String) : Array (Nat × Array String) := Id.run do
  let mut out := #[]
  let mut fence := false
  for (line, k) in (pyLines text).zipIdx do
    if line.trimAscii.startsWith "```" then
      fence := !fence
      continue
    if fence then continue
    let parts := line.splitOn "`"
    let mut spans := #[]
    for (p, i) in parts.zipIdx do
      if i % 2 == 1 && i + 1 < parts.length then spans := spans.push p
    if !spans.isEmpty then out := out.push (k + 1, spans)
  return out

/-- Citation keys `[Key]` of a docstring that are keys of the bibliography. -/
def citedKeys (bib : Std.HashMap String (String × String)) (doc : String) : Array String :=
  Id.run do
    let mut out := #[]
    for p in (doc.splitOn "[").drop 1 do
      match p.splitOn "]" with
      | k :: _ :: _ => if bib.contains k then out := out.push k
      | _ => pure ()
    return out

/-- The text with comments (`--`, nested `/- -/`, docstrings) and string literals replaced by
spaces, line breaks kept. -/
def blankComments (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := Array.mkEmpty cs.size
  let mut depth := 0
  let mut line := false
  let mut str := false
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let n := cs.getD (i + 1) ' '
    if c == '\n' then
      line := false
      out := out.push c
      i := i + 1
    else if line then
      out := out.push ' '; i := i + 1
    else if depth > 0 then
      if c == '/' && n == '-' then depth := depth + 1; out := out.push ' ' |>.push ' '; i := i + 2
      else if c == '-' && n == '/' then
        depth := depth - 1; out := out.push ' ' |>.push ' '; i := i + 2
      else out := out.push ' '; i := i + 1
    else if str then
      if c == '\\' then out := out.push ' ' |>.push ' '; i := i + 2
      else
        if c == '"' then str := false
        out := out.push ' '; i := i + 1
    else if c == '/' && n == '-' then depth := 1; out := out.push ' ' |>.push ' '; i := i + 2
    else if c == '-' && n == '-' then line := true; out := out.push ' ' |>.push ' '; i := i + 2
    else if c == '"' then str := true; out := out.push ' '; i := i + 1
    else out := out.push c; i := i + 1
  return String.ofList out.toList

/-- A line ending a command prefix `… in`. -/
def endsWithIn (l : String) : Bool :=
  let t := (l.trimAscii).toString
  t == "in" || t.endsWith " in" || t.endsWith ")in" || t.endsWith "]in"

/-- A line starting a command prefix (`omit`, `variable`, `open`, `include`, `set_option`,
`attribute`). -/
def isPrefixStart (l : String) : Bool :=
  let t := (l.trimAscii).toString
  ["omit ", "variable ", "open ", "include ", "set_option ", "attribute ", "open scoped ",
    "unseal "].any fun (p : String) => t.startsWith p

structure Grp where
  mod : Name
  start : Nat × Nat
  stop : Nat × Nat
  primary : Name
  members : Array Name := #[]
deriving Inhabited

def tsvLine (fs : List String) : String := "\t".intercalate fs ++ "\n"

def writeTsv (dir : System.FilePath) (file : String) (header : List String)
    (rows : Array (List String)) : IO Unit := do
  let mut s := tsvLine header
  for r in rows do s := s ++ tsvLine r
  IO.FS.writeFile (dir / file) s

def run (env : Environment) (outDir : System.FilePath) (allDocs modDocs : Bool) : IO Report := do
  IO.FS.createDirAll outDir
  let cs := feecConstants env
  let mut info : Std.HashMap Name (Name × ConstantInfo) := {}
  for (nm, mod, ci) in cs do info := info.insert nm (mod, ci)
  -- own ranges
  let ranges ← runCore env do
    let mut r : Std.HashMap Name DeclarationRange := {}
    for (nm, _, _) in cs do
      if let some dr ← findDeclarationRangesCore? nm then r := r.insert nm dr.range
    return r
  -- groups: per module, nested ranges join the outer one
  let mut byMod : Std.HashMap Name (Array (Name × DeclarationRange)) := {}
  for (nm, mod, _) in cs do
    if let some r := ranges[nm]? then byMod := byMod.insert mod ((byMod.getD mod #[]).push (nm, r))
  let mut groups : Array Grp := #[]
  let mut grpOf : Std.HashMap Name Nat := {}
  for (mod, arr) in byMod.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let arr := arr.qsort fun (n1, a) (n2, b) =>
      let ka := posKey a.pos; let kb := posKey b.pos
      if ka != kb then leKey ka kb
      else if posKey a.endPos != posKey b.endPos then leKey (posKey b.endPos) (posKey a.endPos)
      else n1.toString.length < n2.toString.length
    let mut cur? : Option Nat := none
    for (nm, r) in arr do
      let inside := match cur? with
        | some g => leKey groups[g]!.start (posKey r.pos) && leKey (posKey r.endPos) groups[g]!.stop
        | none => false
      if inside then
        grpOf := grpOf.insert nm cur?.get!
      else
        groups := groups.push { mod, start := posKey r.pos, stop := posKey r.endPos, primary := nm }
        cur? := some (groups.size - 1)
        grpOf := grpOf.insert nm (groups.size - 1)
  -- constants without a range join their nearest ranged prefix
  let mut orphans := 0
  let mut orphanNames : Array Name := #[]
  for (nm, _, _) in cs do
    if grpOf.contains nm then continue
    let mut p := nm.getPrefix
    let mut found := false
    while !p.isAnonymous && !found do
      -- the auxiliaries of a public declaration may carry a private prefix
      for q in [p, privateToUserName p] do
        if !found && ranges.contains q then
          if let some g := grpOf[q]? then
            grpOf := grpOf.insert nm g
            found := true
      p := p.getPrefix
    if !found then
      orphans := orphans + 1
      orphanNames := orphanNames.push nm
  for (nm, _, _) in cs do
    if let some g := grpOf[nm]? then
      groups := groups.modify g fun gr => { gr with members := gr.members.push nm }
  -- auxiliary: as in the snapshot, judged on the user-facing name (`isInternal` holds for every
  -- private name)
  let isAux (nm : Name) : Bool :=
    let u := privateToUserName nm
    isAuxRecursor env nm || isNoConfusion env nm || Meta.isMatcherCore env nm ||
      Snapshot.isAuxDecl env u
  -- suffix index of user-facing names
  let mut suffix : Std.HashMap String (Array Name) := {}
  for (nm, _, _) in cs do
    if isAux nm || !grpOf.contains nm then continue
    let comps := (privateToUserName nm).components.toArray.map (·.toString (escape := false))
    for k in [1:comps.size + 1] do
      let s := ".".intercalate (comps.extract (comps.size - k) comps.size).toList
      suffix := suffix.insert s ((suffix.getD s #[]).push nm)
  -- seeds
  let mut seeds : Std.HashMap Name (Array String) := {}
  let addSeed (s : Std.HashMap Name (Array String)) (n : Name) (why : String) :
      Std.HashMap Name (Array String) :=
    let a := s.getD n #[]
    if a.contains why then s else s.insert n (a.push why)
  -- 1. main rows of old_theorems.tsv, through map.tsv
  let mut mainOld : Std.HashSet String := {}
  for line in pyLines (← readText "docs/migration/old_theorems.tsv") do
    let f := line.splitOn "\t"
    if f.length > 2 && f[2]! == "main" then mainOld := mainOld.insert f[0]!
  let resolve (s : String) : Option Name :=
    let n := MapCheck.nameOfString s
    if env.contains n then some n else
      (ResolveName.resolveGlobalName env {} .anonymous [] n).findSome? fun (d, fs) =>
        if fs.isEmpty && env.contains d then some d else none
  let mapLines := pyLines (← readText "docs/migration/map.tsv")
  let mut nMainSeeds := 0
  for line in mapLines.extract 1 mapLines.size do
    let [o, n, _] := line.splitOn "\t" | continue
    if mainOld.contains o && n != "-" then
      if let some c := resolve n then
        if info.contains c then
          seeds := addSeed seeds c "main"
          nMainSeeds := nMainSeeds + 1
  -- 2. doc tokens
  let docFiles ← do
    let base :=
      #["README.md", "docs/OVERVIEW.md", "docs/THESIS_MAP.md", "docs/THESIS_REFERENCES.md"]
    if allDocs then
      let more := (← System.FilePath.readDir "docs").filterMap fun e =>
        if e.fileName.endsWith ".md" then some s!"docs/{e.fileName}" else none
      pure (base ++ (more.filter (!base.contains ·)).qsort (· < ·))
    else pure base
  let mut tokRows : Array (List String) := #[]
  for file in docFiles do
    for (ln, spans) in backtickSpans (← readText file) do
      let mut prev : Option String := none
      for sp in spans do
        for t0 in idTokens sp do
          let t := if t0.startsWith "_" then (prev.getD "") ++ t0 else t0
          if !t0.startsWith "_" then prev := some t0
          let variants := if (t.splitOn "PMC").length > 1 then [t, t.replace "PMC" "PEC"] else [t]
          for v in variants do
            let comps := v.splitOn "."
            let mut hits : Array Name := #[]
            for k in [0:comps.length] do
              let s := ".".intercalate (comps.drop k)
              hits := suffix.getD s #[]
              if !hits.isEmpty then break
            for h in hits do seeds := addSeed seeds h s!"doc:{file}"
            tokRows := tokRows.push [file, toString ln, v, toString hits.size,
              ", ".intercalate ((hits.extract 0 3).toList.map nameStr)]
  -- 2'. module and section docstrings (`/-! … -/`): names in them resolve in their own module
  -- first, then anywhere
  let mut nModDoc := 0
  let mut modDocNamed : Std.HashSet Name := {}
  do
    for f in ← leanFiles "Feec" do
      let mod := (moduleOfPath f).toName
      let txt ← readText f
      for blk in (txt.splitOn "/-!").drop 1 do
        let body := (blk.splitOn "-/").headD ""
        for (_, spans) in backtickSpans body do
          for sp in spans do
            for t in idTokens sp do
              let comps := t.splitOn "."
              let mut hits : Array Name := #[]
              for k in [0:comps.length] do
                let all := suffix.getD (".".intercalate (comps.drop k)) #[]
                let own := all.filter fun n => (info[n]?.map (·.1)) == some mod
                hits := if own.isEmpty then all else own
                if !hits.isEmpty then break
              for h in hits do
                modDocNamed := modDocNamed.insert h
                if modDocs then
                  if !seeds.contains h then nModDoc := nModDoc + 1
                  seeds := addSeed seeds h "moddoc"
  -- 3. docstrings citing a work
  let bib ← match ← Citations.readBib with
    | .ok b => pure b
    | .error e => throw (IO.userError e)
  let mut nCite := 0
  let mut nCiteThm := 0
  for (nm, _, ci) in cs do
    if isAux nm || !grpOf.contains nm then continue
    let some doc ← findDocString? env nm | continue
    let ks := citedKeys bib doc
    if !ks.isEmpty then
      seeds := addSeed seeds nm "cite"
      nCite := nCite + 1
      if ci matches .thmInfo _ then nCiteThm := nCiteThm + 1
  -- 4. metaprograms and coercions
  for (nm, _, ci) in cs do
    let hd := ci.type.getForallBody.getAppFn.constName?
    if let some h := hd then
      let root := (h.components.head?.map (·.toString (escape := false))).getD ""
      if metaRoots.contains root && !(ci matches .thmInfo _) &&
          !(Meta.isInstanceCore env nm) then
        seeds := addSeed seeds nm "meta"
      if Meta.isInstanceCore env nm && coeClasses.contains h then
        seeds := addSeed seeds nm "coe"
  -- source text: occurrences of last name components, in code (comments and strings blanked)
  -- and anywhere
  let files ← leanFiles "Feec"
  let mut srcLines : Std.HashMap String Nat := {}
  let mut rawLines : Std.HashMap Name (Array String) := {}
  let mut occ : Std.HashMap String (Array (Name × Nat)) := {}
  let mut occCode : Std.HashMap String (Array (Name × Nat)) := {}
  for f in files do
    let mod := moduleOfPath f
    let txt ← readText f
    let ls := pyLines txt
    srcLines := srcLines.insert mod ls.size
    rawLines := rawLines.insert mod.toName ls
    for (l, k) in ls.zipIdx do
      for t in idTokens l do
        let last := (t.splitOn ".").getLast!
        occ := occ.insert last ((occ.getD last #[]).push (mod.toName, k + 1))
    for (l, k) in (pyLines (blankComments txt)).zipIdx do
      for t in idTokens l do
        let last := (t.splitOn ".").getLast!
        occCode := occCode.insert last ((occCode.getD last #[]).push (mod.toName, k + 1))
  -- deletion range of a group: its declaration range, extended upwards over the command
  -- prefixes `omit … in`, `variable … in`, `open … in`, … that apply to it alone
  let delStart (g : Grp) : Nat := Id.run do
    let ls := rawLines.getD g.mod #[]
    let mut a := g.start.1
    let mut again := true
    while again do
      again := false
      if a ≥ 2 && endsWithIn (ls.getD (a - 2) "") then
        -- the prefix may span several lines: find the line that starts it
        let mut b := a - 1
        let mut found := false
        for _ in [0:8] do
          if b ≥ 1 && isPrefixStart (ls.getD (b - 1) "") then
            found := true
            break
          if b ≤ 1 then break
          b := b - 1
        if found then
          a := b
          again := true
    return a
  -- closure over groups; then protect the dead groups that the closure cannot see used:
  -- instances (elaboration may need them without leaving a trace) and groups whose name occurs
  -- in code outside dead groups (`simp only [rfl_lemma]`, `change`, `show`, `unfold`, simp
  -- arguments that do not fire); repeat until nothing new is protected
  let mut liveGrp : Std.HashSet Nat := {}
  let mut visited : Std.HashSet Name := {}
  let mut stack : Array Name := seeds.keys.toArray
  let mut nProtInst := 0
  let mut nProtRef := 0
  let mut rounds := 0
  repeat
    rounds := rounds + 1
    while !stack.isEmpty do
      let c := stack.back!
      stack := stack.pop
      if visited.contains c then continue
      visited := visited.insert c
      let some (_, ci) := info[c]? | continue
      if let some g := grpOf[c]? then
        if !liveGrp.contains g then
          liveGrp := liveGrp.insert g
          for m in groups[g]!.members do
            if !visited.contains m then stack := stack.push m
      for d in ci.getUsedConstantsAsSet do
        if info.contains d && !visited.contains d then stack := stack.push d
    let mut dl : Std.HashMap Name (Array (Nat × Nat)) := {}
    for (g, i) in groups.zipIdx do
      if !liveGrp.contains i then
        dl := dl.insert g.mod ((dl.getD g.mod #[]).push (delStart g, g.stop.1))
    let inDead0 (mod : Name) (l : Nat) : Bool :=
      (dl.getD mod #[]).any fun (a, b) => a ≤ l && l ≤ b
    let mut newSeeds : Array (Name × String) := #[]
    for (g, i) in groups.zipIdx do
      if liveGrp.contains i then continue
      if g.members.any (Meta.isInstanceCore env ·) then
        newSeeds := newSeeds.push (g.primary, "instance")
        nProtInst := nProtInst + 1
        continue
      let mut hit : Option String := none
      for m in g.members do
        if isAux m || hit.isSome then continue
        let lc := lastComp m
        if lc.isEmpty then continue
        for (mod, l) in occCode.getD lc #[] do
          if !inDead0 mod l then
            hit := some s!"{pathOfModule mod}:{l}"
            break
      if let some loc := hit then
        newSeeds := newSeeds.push (g.primary, s!"coderef {loc}")
        nProtRef := nProtRef + 1
    if newSeeds.isEmpty then break
    for (n, why) in newSeeds do
      seeds := addSeed seeds n why
      stack := stack.push n
  let seedGrp : Std.HashSet Nat := seeds.keys.foldl (init := {}) fun s n =>
    match grpOf[n]? with | some g => s.insert g | none => s
  let status (g : Nat) : String :=
    if seedGrp.contains g then "seed" else if liveGrp.contains g then "live" else "dead"
  let statusOf (n : Name) : String := match grpOf[n]? with | some g => status g | none => "orphan"
  -- reverse edges between groups: `usersOf g` = the groups with a member using a member of `g`
  let mut usersOf : Std.HashMap Nat (Std.HashSet Nat) := {}
  for (nm, _, ci) in cs do
    let some g := grpOf[nm]? | continue
    for d in ci.getUsedConstantsAsSet do
      if let some h := grpOf[d]? then
        if h != g then usersOf := usersOf.insert h ((usersOf.getD h {}).insert g)
  /- the modules of the users of the group of `n` (other than its own module), sorted -/
  let userMods (g : Nat) : Array String :=
    let ms := (usersOf.getD g {}).fold (init := (∅ : Std.HashSet String)) fun acc u =>
      if groups[u]!.mod == groups[g]!.mod then acc else acc.insert (nameStr groups[u]!.mod)
    ms.toArray.qsort (· < ·)
  let nUsers (g : Nat) : Nat := (usersOf.getD g {}).size
  -- group kinds and primaries
  let grpKind (g : Grp) : String :=
    match info[g.primary]? with
    | some (_, ci) =>
      if Meta.isInstanceCore env g.primary then "instance"
      else if isStructure env g.primary then "structure" else kindStr ci
    | none => "?"
  let grpLines (g : Grp) : Nat := g.stop.1 - g.start.1 + 1
  -- dead line ranges per module
  let mut deadLines : Std.HashMap Name (Array (Nat × Nat)) := {}
  for (g, i) in groups.zipIdx do
    if status i == "dead" then
      deadLines := deadLines.insert g.mod ((deadLines.getD g.mod #[]).push (delStart g, g.stop.1))
  let inDead (mod : Name) (l : Nat) : Bool :=
    (deadLines.getD mod #[]).any fun (a, b) => a ≤ l && l ≤ b
  -- simp lemmas proved by rfl
  let simpRfl ← runCore env do
    let st ← MetaM.run' getSimpTheorems
    let mut s : Std.HashSet Name := {}
    for (nm, _, ci) in cs do
      if let .thmInfo v := ci then
        if isRflProof v.value && st.isLemma (.decl nm) then s := s.insert nm
    return s
  -- map.tsv rows by new name
  let mut rowsOfNew : Std.HashMap Name (Array (Nat × String × String)) := {}
  let mut oldRows : Std.HashMap String (Array Name) := {}
  for (line, k) in mapLines.zipIdx do
    if k == 0 then continue
    let [o, n, kind] := line.splitOn "\t" | continue
    if n == "-" then continue
    if let some c := resolve n then
      rowsOfNew := rowsOfNew.insert c ((rowsOfNew.getD c #[]).push (k + 1, o, kind))
      oldRows := oldRows.insert o ((oldRows.getD o #[]).push c)
  -- wrappers
  let mut wrapperOf : Std.HashMap Name (Name × String) := {}
  let mut wrapRows : Array (List String) := #[]
  for (nm, mod, ci) in cs do
    if isAux nm || !ranges.contains nm then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let some g := grpOf[nm]? | continue
    let tyC := ci.type.getUsedConstantsAsSet
    let vC := v.getUsedConstantsAsSet
    let extra := vC.toArray.filter fun c => !tyC.contains c && c != nm
    if extra.any (fun c => grpOf[c]? == some g) then continue
    let fe := extra.filter info.contains
    if fe.any isAux then continue
    let nonGlue := extra.filter fun c => !info.contains c && !glue.contains c
    let target? : Option (Name × String) :=
      if fe.size == 1 && nonGlue.isEmpty then
        some (fe[0]!, if extra.size == 1 then "exact" else "glue")
      else if fe.isEmpty && nonGlue.size == 1 then some (nonGlue[0]!, "external")
      else none
    let some (t, wk) := target? | continue
    -- the body must be an application whose head is the target or glue
    let hd := (stripLams v).getAppFn.constName?
    unless hd == some t || (hd.map glue.contains).getD false do continue
    wrapperOf := wrapperOf.insert nm (t, wk)
    let tmod := (info[t]?.map (·.1)).getD .anonymous
    wrapRows := wrapRows.push [nameStr nm, nameStr mod, kindStr ci, statusOf nm,
      if seeds.contains nm then ",".intercalate (seeds.getD nm #[]).toList else "",
      nameStr t, if info.contains t then nameStr tmod else "(external)",
      if info.contains t then statusOf t else "external", wk,
      if !info.contains t then "external"
      else if dirOf tmod == dirOf mod then "same-dir" else "cross-dir",
      toString (nUsers g), " ".intercalate (userMods g).toList]
  -- duplicates
  let mut buckets : Std.HashMap UInt64 (Array (Name × Expr × Option Expr)) := {}
  for (nm, _, ci) in cs do
    if isAux nm || !ranges.contains nm then continue
    let ls := ci.levelParams.map fun _ => Level.zero
    let ty := ci.type.instantiateLevelParams ci.levelParams ls
    match ci with
    | .thmInfo _ =>
      let h := mixHash 7 ty.hash
      buckets := buckets.insert h ((buckets.getD h #[]).push (nm, ty, none))
    | .defnInfo d =>
      let v := d.value.instantiateLevelParams ci.levelParams ls
      let h := mixHash (mixHash 11 ty.hash) v.hash
      buckets := buckets.insert h ((buckets.getD h #[]).push (nm, ty, some v))
    | _ => pure ()
  let mut dupRows : Array (List String) := #[]
  let mut dupOf : Std.HashMap Name (Array Name) := {}
  let mut nDupSets := 0
  for (_, arr) in buckets.toArray do
    if arr.size < 2 then continue
    -- split the bucket into classes of equal entries
    let mut classes : Array (Array Name) := #[]
    let mut reps : Array (Expr × Option Expr) := #[]
    for (nm, ty, v) in arr do
      match reps.findIdx? (fun (t, w) => t == ty && w == v) with
      | some i => classes := classes.modify i (·.push nm)
      | none => classes := classes.push #[nm]; reps := reps.push (ty, v)
    for cl in classes do
      if cl.size < 2 then continue
      nDupSets := nDupSets + 1
      for n in cl do
        dupOf := dupOf.insert n (cl.filter (· != n))
        let (mod, ci) := info[n]!
        let gn := (grpOf[n]?).getD 0
        dupRows := dupRows.push [toString nDupSets, nameStr n, nameStr mod, kindStr ci, statusOf n,
          if seeds.contains n then ",".intercalate (seeds.getD n #[]).toList else "",
          toString (nUsers gn), " ".intercalate (userMods gn).toList]
  -- largest
  let mut bigRows : Array (Nat × List String) := #[]
  for (nm, mod, ci) in cs do
    if isAux nm then continue
    let some r := ranges[nm]? | continue
    let some v := ci.value? (allowOpaque := true) | continue
    unless ci matches .thmInfo _ || ci matches .defnInfo _ do continue
    let lines := r.endPos.line - r.pos.line + 1
    let sz ← v.numObjs
    bigRows := bigRows.push (lines, [nameStr nm, nameStr mod, dirOf mod, kindStr ci,
      toString lines, toString sz, statusOf nm])
  bigRows := bigRows.qsort fun a b => a.1 > b.1
  -- name twins: kept proofs of at least 20 lines sharing their last name component (up to
  -- primes) in different namespaces, usually copies to be generalized and merged
  let mut twinMap : Std.HashMap String (Array (List String)) := {}
  for (lines, r) in bigRows do
    if lines < 20 || r[6]! == "dead" then continue
    let k := String.ofList ((lastComp (r[0]!.toName)).toList.reverse.dropWhile (· == '\'')).reverse
    twinMap := twinMap.insert k ((twinMap.getD k #[]).push r)
  let mut twinSets : Array (Nat × String × Array (List String)) := #[]
  for (k, rs) in twinMap.toArray do
    if rs.size < 2 then continue
    let tot := rs.foldl (init := 0) fun a r => a + (r[4]!.toNat?.getD 0)
    twinSets := twinSets.push (tot, k, rs)
  twinSets := twinSets.qsort fun a b => a.1 > b.1
  let twinRows : Array (List String) := twinSets.foldl (init := #[]) fun acc (tot, k, rs) =>
    acc ++ rs.map fun r => [k, toString tot, r[0]!, r[1]!, r[2]!, r[4]!, r[5]!, r[6]!]
  -- dead groups
  let mut deadRows : Array (List String) := #[]
  let mut mapDeadRows : Array (List String) := #[]
  let mut modStats : Std.HashMap Name (Nat × Nat × Nat × Nat) := {}
  let mut nDeadTextSafe := 0
  for (g, i) in groups.zipIdx do
    let st := status i
    let ln := grpLines g
    let (a, b, c, d) := modStats.getD g.mod (0, 0, 0, 0)
    modStats := modStats.insert g.mod
      (a + 1, b + ln, c + (if st == "dead" then 1 else 0), d + (if st == "dead" then ln else 0))
    if st != "dead" then continue
    let mut refs : Array String := #[]
    let mut seen : Std.HashSet String := {}
    for m in g.members do
      if isAux m then continue
      let lc := lastComp m
      if lc.isEmpty || seen.contains lc then continue
      seen := seen.insert lc
      for (mod, l) in occ.getD lc #[] do
        if !inDead mod l then refs := refs.push s!"{pathOfModule mod}:{l}"
    if refs.isEmpty then nDeadTextSafe := nDeadTextSafe + 1
    let rows := g.members.foldl (init := #[]) fun acc m => acc ++ (rowsOfNew.getD m #[])
    for (k, o, kind) in rows do
      let others := (oldRows.getD o #[]).filter fun c => statusOf c != "dead"
      let action :=
        if !others.isEmpty then s!"drop-row (also mapped to {nameStr others[0]!})"
        else
          let n := (g.members.find? fun m => (rowsOfNew.getD m #[]).any (·.1 == k)).getD g.primary
          let viaW := (wrapperOf[n]?).bind fun (t, _) =>
            if info.contains t && statusOf t != "dead" then some t else none
          let viaD := ((dupOf.getD n #[]).find? fun t => statusOf t != "dead")
          match viaW <|> viaD with
          | some t => s!"repoint {nameStr t} (dedup)"
          | none => if mainOld.contains o then "MAIN: must repoint" else "deleted-helper"
      mapDeadRows := mapDeadRows.push [toString k, o, nameStr g.primary, kind, action]
    deadRows := deadRows.push [pathOfModule g.mod, toString (delStart g), toString g.stop.1,
      toString (g.stop.1 + 1 - delStart g), grpKind g, nameStr g.primary,
      if isPrivateName g.primary then "private" else "",
      toString g.members.size, toString refs.size, ", ".intercalate (refs.extract 0 3).toList,
      if g.members.any simpRfl.contains then "rflSimp" else "",
      ", ".intercalate (rows.toList.map fun (k, _, _) => s!"map.tsv:{k}"),
      toString (nUsers i), " ".intercalate (userMods i).toList,
      if g.members.any modDocNamed.contains then "moddoc" else ""]
  -- per-module and per-directory stats
  let mut modRows : Array (List String) := #[]
  let mut dirStats : Std.HashMap String (Nat × Nat × Nat × Nat × Nat × Nat) := {}
  for (mod, (a, b, c, d)) in modStats.toArray.qsort (fun x y => x.1.toString < y.1.toString) do
    let src := srcLines.getD (nameStr mod) 0
    modRows := modRows.push [pathOfModule mod, toString src, toString a, toString b, toString c,
      toString d]
    let dir := dirOf mod
    let (m, s, ga, gl, da, dl) := dirStats.getD dir (0, 0, 0, 0, 0, 0)
    dirStats := dirStats.insert dir (m + 1, s + src, ga + a, gl + b, da + c, dl + d)
  -- metrics
  let mut totalLines := 0
  for (_, n) in srcLines.toArray do totalLines := totalLines + n
  let userDecls := cs.filter fun (nm, _, _) => !isAux nm && ranges.contains nm
  let nThm := (userDecls.filter fun (_, _, ci) => ci matches .thmInfo _).size
  let nPriv := (userDecls.filter fun (nm, _, _) => isPrivateName nm).size
  let nDead := (groups.zipIdx.filter fun (_, i) => status i == "dead").size
  let deadLn := groups.zipIdx.foldl (init := 0) fun s (g, i) =>
    if status i == "dead" then s + grpLines g else s
  let deadThm :=
    (groups.zipIdx.filter fun (g, i) => status i == "dead" && grpKind g == "theorem").size
  let liveWrappers := wrapRows.filter fun r => r[3]! != "dead"
  -- write
  writeTsv outDir "dead.tsv" ["file", "line", "endLine", "lines", "kind", "name", "private",
    "members", "textrefs", "firstTextRefs", "rflSimp", "mapRows", "deadUsers",
    "deadUserModules", "modDoc"] deadRows
  writeTsv outDir "dead_by_module.tsv" ["file", "sourceLines", "groups", "groupLines", "deadGroups",
    "deadLines"] modRows
  writeTsv outDir "keep_seeds.tsv" ["name", "status", "reasons"] <|
    (seeds.toArray.qsort (fun a b => a.1.toString < b.1.toString)).map fun (n, r) =>
      [nameStr n, statusOf n, ",".intercalate r.toList]
  writeTsv outDir "dups.tsv" ["set", "name", "module", "kind", "status", "seed", "users",
    "userModules"] dupRows
  writeTsv outDir "wrappers.tsv" ["name", "module", "kind", "status", "seed", "target",
    "targetModule", "targetStatus", "wrapKind", "scope", "users", "userModules"] wrapRows
  writeTsv outDir "largest.tsv" ["name", "module", "dir", "kind", "lines", "termSize", "status"]
    (bigRows.map (·.2))
  writeTsv outDir "twins.tsv" ["key", "setLines", "name", "module", "dir", "lines", "termSize",
    "status"] twinRows
  writeTsv outDir "map_dead.tsv" ["mapLine", "old", "new", "kind", "action"] mapDeadRows
  writeTsv outDir "orphans.tsv" ["name", "module", "kind", "reached"] <| orphanNames.map fun n =>
    [nameStr n, nameStr ((info[n]?.map (·.1)).getD .anonymous),
      (info[n]?.map (kindStr ·.2)).getD "?", if visited.contains n then "yes" else "no"]
  writeTsv outDir "doc_tokens.tsv" ["file", "line", "token", "matches", "examples"] tokRows
  let dirRows := (dirStats.toArray.qsort (fun a b => a.1 < b.1)).map
    fun (d, (m, s, ga, gl, da, dl)) =>
    s!"| `{d}` | {m} | {s} | {ga} | {gl} | {da} | {dl} |"
  let summary := String.join [
    "# feec-deps summary\n\n",
    s!"- modules: {srcLines.size}; source lines: {totalLines}\n",
    s!"- constants in Feec modules: {cs.size} (orphans without a ranged owner: {orphans})\n",
    s!"- user declarations (own range, not auxiliary): {userDecls.size}; theorems {nThm}; \
      private {nPriv}\n",
    s!"- source groups: {groups.size}; live {liveGrp.size}; seed groups {seedGrp.size}\n",
    s!"- seeds: {seeds.size} constants (main via map.tsv {nMainSeeds} rows; citing docstrings \
      {nCite}, of which theorems {nCiteThm}; only from module docstrings {nModDoc})\n",
    s!"- protected after the closure ({rounds} rounds): instances {nProtInst}, groups named in \
      code outside dead groups {nProtRef}\n",
    s!"- DEAD groups: {nDead} ({deadThm} theorems), {deadLn} lines; with no text reference \
      outside dead code: {nDeadTextSafe}\n",
    s!"- wrappers: {wrapRows.size} (not dead: {liveWrappers.size}); duplicate sets: {nDupSets}; \
      name-twin sets: {twinSets.size} ({twinSets.foldl (init := 0) fun a t => a + t.1} lines)\n",
    s!"- map.tsv rows whose new declaration is dead: {mapDeadRows.size}\n\n",
    "| dir | modules | source lines | groups | group lines | dead groups | dead lines |\n",
    "|---|---|---|---|---|---|---|\n",
    "\n".intercalate dirRows.toList, "\n"]
  IO.FS.writeFile (outDir / "summary.md") summary
  return ({ name := "feec-deps" } : Report).addInfo summary

/-- `--strip FILE OUT [DIR]`: write `FILE` without the deletion ranges (`line`–`endLine`) of its
rows in `DIR/dead.tsv` (default `.lake/feec-deps`) to `OUT` (which may be `FILE`), dropping the
blank line that followed each deleted range. -/
def strip (file out : String) (dir : System.FilePath := ".lake/feec-deps") : IO UInt32 := do
  let mut kill : Std.HashSet Nat := {}
  let mut n := 0
  for row in (pyLines (← readText (dir / "dead.tsv"))).extract 1 do
    let f := (row.splitOn "\t").toArray
    if f.size < 3 || f[0]! != file then continue
    let some a := f[1]!.toNat? | continue
    let some b := f[2]!.toNat? | continue
    n := n + 1
    for l in [a:b + 1] do kill := kill.insert l
  let ls := pyLines (← readText file)
  let mut outLs : Array String := #[]
  for (l, k) in ls.zipIdx do
    let i := k + 1
    if kill.contains i then continue
    -- a blank line right after a deleted range goes with it
    let prevBlank := (outLs.back?.map (·.trimAscii.isEmpty)).getD true
    if l.trimAscii.isEmpty && kill.contains (i - 1) && prevBlank then continue
    outLs := outLs.push l
  IO.FS.writeFile out (String.intercalate "\n" outLs.toList ++ "\n")
  IO.println s!"{file}: {n} dead groups, {ls.size - outLs.size} lines removed -> {out}"
  return 0

def main (args : List String) : IO UInt32 := do
  if let "--strip" :: file :: out :: rest := args then
    return ← match rest with
      | [] => strip file out
      | [dir] => strip file out dir
      | _ => do IO.eprintln "usage: lake exe feec-deps --strip FILE OUT [DIR]"; return 2
  let flags := ["--core-docs", "--moddoc"]
  let allDocs := !args.contains "--core-docs"
  let modDocs := args.contains "--moddoc"
  let out? : Option String := match args.filter (!flags.contains ·) with
    | [] => some ".lake/feec-deps"
    | [o] => if o.startsWith "-" then none else some o
    | _ => none
  let some out := out? | do
    IO.eprintln "usage: lake exe feec-deps [--core-docs] [--moddoc] [OUT_DIR]"
    return 2
  (← run (← loadFeec) out allDocs modDocs).print
  return 0

end FeecCheck.Deps
