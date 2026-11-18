module

public import FeecCheck.Util

/-!
# Palomar gate

`lake exe feec-palomar` (also run by `lake exe feec-gate`). Checks the Palomar submission
packages, the directories `palomar/*/` with a `comparator.json` (`palomarPackages`; README,
"Palomar submission"); in each:

1. every shared block of `Challenge.lean`, the lines between `-- palomar-shared: <name>` and
   `-- palomar-shared-end: <name>`, is byte-identical to the block `<name>` of the canonical file
   `palomar/shared/vocabulary.lean.txt` (`sharedPath`): the notions that several challenges
   state are stated identically. The markers are well formed (at the start of their line, no
   nesting, no repeated name, every block closed), every canonical block is copied by some
   challenge, and no challenge declares outside its blocks a name of a canonical block (up to the
   namespaces around the block): a shared notion is stated only by its block.
2. `Solution/Defs.lean` is the copy of the definitions of `Challenge.lean`: the same imports and,
   after the module docstring, the same text with the compared theorems (the names of
   `theorem_names` in `comparator.json`, declared fully qualified or inside their namespaces;
   each with its docstring, statement and proof, up to the next blank line) removed. The module
   docstring of `Defs.lean` is its own.
3. `lake build` in the package succeeds (its bridges to `Feec` still compile), with no warning but
   the `sorry` of `Challenge.lean`.

`lake exe feec-palomar --write` copies the canonical blocks into the challenges whose markers are
well formed, then regenerates `Defs.lean` from each challenge, keeping its docstring;
`--no-build` skips the builds.

The comparator (`lake comparator` in a package, several minutes) is not run here: it judges the
solution against the challenge before a submission.
-/

public section

namespace FeecCheck.Palomar

/-- The lines before the module docstring, the module docstring (`/-!` to the first line `-/`)
and the lines after it. -/
def splitDoc (ls : Array String) : Option (Array String × Array String × Array String) := do
  let i ← ls.findIdx? (·.startsWith "/-!")
  let j ← (ls.extract i ls.size).findIdx? (· == "-/")
  return (ls.extract 0 i, ls.extract i (i + j + 1), ls.extract (i + j + 1) ls.size)

/-- The text without the theorem `name`: from the docstring opening before `theorem n ` to the
next blank line, inclusive, where `n` is the longest dotted suffix of `name` (`A.B.c`, `B.c`,
`c`) declared so, whatever the enclosing namespaces. -/
def dropTheorem (name : String) (ls : Array String) : Option (Array String) := do
  let parts := name.splitOn "."
  let t ← (List.range parts.length).findSome? fun k =>
    ls.findIdx? (·.startsWith s!"theorem {".".intercalate (parts.drop k)} ")
  let d ← ((ls.extract 0 t).toList.reverse.findIdx? (·.startsWith "/--")).map (t - 1 - ·)
  let b := ((ls.extract t ls.size).findIdx? (· == "")).getD (ls.size - t)
  return ls.extract 0 d ++ ls.extract (t + b + 1) ls.size

/-- The compared theorems: the entries of `theorem_names` in `comparator.json`, fully qualified
(`FEEC.staticFEEC`). -/
def theoremNames (json : String) : Option (List String) :=
  match json.splitOn "\"theorem_names\": [" with
  | [_, rest] => do
    let names := ((rest.splitOn "]").headD "").splitOn "," |>.map fun n =>
      String.ofList (n.toList.filter fun c => c != '"' && !c.isWhitespace)
    if names.any (·.isEmpty) then none else some names
  | _ => none

/-- The expected `Defs.lean`: the imports and the body of the challenge (without the theorems)
around the module docstring of the current `Defs.lean`. -/
def expected (pkg : System.FilePath) (names : List String) (chal cur : String) :
    Except String String := do
  let some (imps, _, body) := splitDoc (pyLines chal)
    | throw s!"{pkg / "Challenge.lean"}: no module docstring"
  let some (_, doc, _) := splitDoc (pyLines cur)
    | throw s!"{pkg / "Solution" / "Defs.lean"}: no module docstring"
  let body ← names.foldlM (init := body) fun body name => do
    let some body := dropTheorem name body
      | throw s!"{pkg / "Challenge.lean"}: no `theorem {name}`"
    return body
  return "\n".intercalate (imps ++ doc ++ body).toList ++ "\n"

/-! ### Shared blocks -/

/-- The canonical copies of the shared blocks. -/
def sharedPath : System.FilePath := "palomar" / "shared" / "vocabulary.lean.txt"

/-- The line opening a shared block, followed by its name. -/
def openMarker : String := "-- palomar-shared: "

/-- The line closing a shared block, followed by its name. -/
def closeMarker : String := "-- palomar-shared-end: "

/-- A shared block of a file: its name, the (1-based) line of its opening marker and the lines
between its markers. -/
structure Block where
  name : String
  line : Nat
  body : Array String

/-- The name after the marker `m` on the line `l`, if `l` starts with `m`. -/
def markerName (m l : String) : Option String :=
  if l.startsWith m then some (String.ofList (l.toList.drop m.length)) else none

/-- The shared blocks of the lines `ls` of the file `path`, or the first error
`path:line: message` (a marker inside a block, a closing marker of another block, an unclosed
block, a repeated or empty name, a line `-- palomar-shared…` that is no marker, for instance an
indented one: a marker starts its line). -/
def blocks (path : System.FilePath) (ls : Array String) : Except String (Array Block) := do
  let mut out : Array Block := #[]
  let mut cur : Option Block := none
  for h : i in [0:ls.size] do
    let l := ls[i]
    if let some name := markerName closeMarker l then
      let some b := cur | throw s!"{path}:{i + 1}: `{l}` closes no block"
      unless b.name == name do
        throw s!"{path}:{i + 1}: `{l}` inside the block `{b.name}` of line {b.line}"
      out := out.push b
      cur := none
    else if let some name := markerName openMarker l then
      if let some b := cur then
        throw s!"{path}:{i + 1}: block `{name}` inside the block `{b.name}` of line {b.line}"
      if name.isEmpty || name.any Char.isWhitespace then
        throw s!"{path}:{i + 1}: `{l}`: a block name is one word"
      if let some b := out.find? (·.name == name) then
        throw s!"{path}:{i + 1}: second block `{name}` (the first at line {b.line})"
      cur := some ⟨name, i + 1, #[]⟩
    else if l.trimAscii.startsWith "-- palomar-shared" then
      throw s!"{path}:{i + 1}: `{l}` is no marker, a line `{openMarker}<name>` or \
        `{closeMarker}<name>`"
    else if let some b := cur then
      cur := some { b with body := b.body.push l }
  if let some b := cur then throw s!"{path}:{b.line}: block `{b.name}` is not closed"
  return out

/-- The lines `ls` with the body of every block named in `canon` replaced by its canonical
copy. -/
def syncBlocks (canon : Array Block) (ls : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut skip := false
  for l in ls do
    if skip then
      if (markerName closeMarker l).isSome then
        out := out.push l
        skip := false
    else
      out := out.push l
      if let some name := markerName openMarker l then
        if let some c := canon.find? (·.name == name) then
          out := out ++ c.body
          skip := true
  return out

/-- The errors of the blocks of the challenge `chal` against the canonical blocks: an unknown
name, or the first line where a block differs from its canonical copy. -/
def checkBlocks (chal : System.FilePath) (canon : Array Block) (bs : Array Block) :
    Array String := Id.run do
  let mut errs := #[]
  for b in bs do
    match canon.find? (·.name == b.name) with
    | none => errs := errs.push s!"{chal}:{b.line}: no block `{b.name}` in {sharedPath}"
    | some c =>
      if b.body != c.body then
        let j := ((List.range (max b.body.size c.body.size)).find? fun j =>
          b.body[j]? != c.body[j]?).getD 0
        errs := errs.push s!"{chal}:{b.line + 1 + j}: the block `{b.name}` differs from its \
          canonical copy {sharedPath}:{c.line + 1 + j} (change a notion there, then copy it \
          with `lake exe feec-palomar --write`)"
  return errs

/-- The name declared by the line `l`, if `l` starts with a declaration keyword. -/
def declName (l : String) : Option String :=
  ["def ", "abbrev ", "structure ", "class ", "inductive ", "instance ", "theorem ", "lemma "]
    |>.findSome? fun k =>
      let n := String.ofList ((l.toList.drop k.length).takeWhile fun c =>
        !c.isWhitespace && !"({[:".contains c)
      if l.startsWith k && !n.isEmpty then some n else none

/-- The names declared in the lines `ls`, qualified by the namespaces open at their line
(`namespace`, `section` and `end` lines), with their lines and the shared blocks they lie in;
the lines that start inside a comment `/- ⋯ -/` (docstrings included) declare nothing. -/
def declarations (ls : Array String) : Array (String × Nat × Option String) := Id.run do
  let mut out := #[]
  let mut ns : Array (List String) := #[]
  let mut block : Option String := none
  let mut depth : Int := 0
  for h : i in [0:ls.size] do
    let l := ls[i]
    let inComment := depth > 0
    unless !inComment && l.startsWith "--" do
      depth := depth + ((l.splitOn "/-").length : Int) - (l.splitOn "-/").length
    if inComment then continue
    if let some name := markerName openMarker l then block := some name
    else if (markerName closeMarker l).isSome then block := none
    else if let some n := markerName "namespace " l then ns := ns.push (n.splitOn ".")
    else if l == "section" || l.startsWith "section " || l.endsWith " section" then
      ns := ns.push []
    else if l == "end" || l.startsWith "end " then ns := ns.pop
    else if let some n := declName l then
      out := out.push (".".intercalate (ns.toList.flatten ++ [n]), i + 1, block)
  return out

/-- The errors of the declarations of the challenge `chal` (its lines `ls`) outside its shared
blocks that restate a notion of the canonical blocks, the names `canon` with their blocks (the
name of a canonical declaration, up to the namespaces around the block): a challenge states such
a notion by copying its block. -/
def checkOutside (chal : System.FilePath) (canon : Array (String × String)) (ls : Array String) :
    Array String := Id.run do
  let mut errs := #[]
  for (n, line, block) in declarations ls do
    if block.isNone then
      if let some (r, b) := canon.find? fun (r, _) => n == r || n.endsWith ("." ++ r) then
        errs := errs.push s!"{chal}:{line}: `{n}` restates `{r}` of the shared block `{b}` \
          outside the block; copy the block instead, or rename it"
  return errs

/-! ### The packages -/

/-- `lake build` in `pkg`, outside the environment of the calling `lake exe`. -/
def build (pkg : System.FilePath) : IO (Except String Unit) := do
  let unset := #["LAKE", "LAKE_HOME", "LEAN_PATH", "LEAN_SRC_PATH"].map (·, none)
  let out ← IO.Process.output { cmd := "lake", args := #["build"], cwd := pkg, env := unset }
  let log := out.stdout ++ out.stderr
  if out.exitCode != 0 then
    return .error s!"{pkg}: `lake build` failed (exit {out.exitCode}):\n{log}"
  let bad := (pyLines log).filter fun l => l.startsWith "warning:" &&
    !(l.startsWith "warning: Challenge.lean:" && l.endsWith "declaration uses `sorry`")
  unless bad.isEmpty do
    return .error s!"{pkg}: `lake build` warns:\n{"\n".intercalate bad.toList}"
  return .ok ()

/-- The checks of one package against the canonical blocks `canon`, whose declarations are
`canonDecls`; the names of the shared blocks of its challenge, with the report. -/
def runPackage (pkg : System.FilePath) (canon : Array Block) (canonDecls : Array (String × String))
    (write doBuild : Bool) (rep : Report) : IO (Array String × Report) := do
  let mut rep := rep
  let chalPath := pkg / "Challenge.lean"
  let mut chal ← readText chalPath
  -- only well-formed blocks are copied: the body of an unclosed block runs to the end of the file
  if write && (blocks chalPath (pyLines chal) matches .ok _) then
    let synced := "\n".intercalate (syncBlocks canon (pyLines chal)).toList ++ "\n"
    if synced != chal then
      IO.FS.writeFile chalPath synced
      chal := synced
      rep := rep.addInfo s!"Palomar: wrote the shared blocks of {chalPath}"
  let mut used := #[]
  match blocks chalPath (pyLines chal) with
  | .error e => rep := rep.addError e
  | .ok bs =>
    used := bs.map (·.name)
    for e in checkBlocks chalPath canon bs do rep := rep.addError e
    for e in checkOutside chalPath canonDecls (pyLines chal) do rep := rep.addError e
    rep := rep.addInfo s!"Palomar: shared blocks of {chalPath}: {", ".intercalate used.toList}"
  let defs := pkg / "Solution" / "Defs.lean"
  let some names := theoremNames (← readText (pkg / "comparator.json"))
    | return (used, rep.addError s!"{pkg / "comparator.json"}: no theorem names `Namespace.name`")
  let cur ← readText defs
  match expected pkg names chal cur with
  | .error e => rep := rep.addError e
  | .ok exp =>
    if exp != cur then
      if write then
        IO.FS.writeFile defs exp
        rep := rep.addInfo s!"Palomar: wrote {defs}"
      else
        rep := rep.addError s!"{defs}:1: not the definitions of {chalPath}; \
          regenerate with `lake exe feec-palomar --write`"
  if doBuild then
    if let .error e ← build pkg then rep := rep.addError e
  return (used, rep.addInfo s!"Palomar: {defs} against {", ".intercalate names} of {chalPath}\
    {if doBuild then s!", lake build in {pkg}" else ""}")

def run (write : Bool := false) (doBuild : Bool := true) : IO Report := do
  let mut rep : Report := { name := "Palomar" }
  let shared := pyLines (← readText sharedPath)
  let mut canon : Array Block := #[]
  match blocks sharedPath shared with
  | .ok bs => canon := bs
  | .error e => rep := rep.addError e
  let canonDecls := (declarations shared).filterMap fun (n, _, b) => b.map (n, ·)
  let packages ← palomarPackages
  let mut used : Array String := #[]
  for pkg in packages do
    let (u, r) ← runPackage pkg canon canonDecls write doBuild rep
    used := used ++ u
    rep := r
  for c in canon do
    unless used.contains c.name do
      rep := rep.addError s!"{sharedPath}:{c.line}: the block `{c.name}` is in no challenge"
  return rep.addInfo s!"Palomar: {packages.size} packages, {canon.size} shared blocks, \
    {rep.errors.size} errors"

end FeecCheck.Palomar
