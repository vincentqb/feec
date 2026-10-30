module

public import FeecCheck.Util

/-!
# Palomar gate

`lake exe feec-palomar` (also run by `lake exe feec-gate`). Checks the Palomar submission
packages `palomar/static/`, `palomar/dynamic/` and `palomar/periodic/` (README, "Palomar submission"); in each:

1. `Solution/Defs.lean` is the copy of the definitions of `Challenge.lean`: the same imports and,
   after the module docstring, the same text with the compared theorem (the first name of
   `theorem_names` in `comparator.json`; its docstring, statement and proof, up to the next blank
   line) removed. The module docstring of `Defs.lean` is its own. `lake exe feec-palomar --write`
   regenerates `Defs.lean` from the challenge, keeping that docstring.
2. `lake build` in the package succeeds (its bridge `Solution/Bridge.lean` still compiles against
   `Feec`), with no warning but the `sorry` of `Challenge.lean`.

The comparator (`lake comparator` in a package, several minutes) is not run here: it judges the
solution against the challenge before a submission.
-/

public section

namespace FeecCheck.Palomar

/-- The submission packages. -/
def packages : Array System.FilePath := #["palomar/static", "palomar/dynamic", "palomar/periodic"]

/-- The lines before the module docstring, the module docstring (`/-!` to the first line `-/`)
and the lines after it. -/
def splitDoc (ls : Array String) : Option (Array String × Array String × Array String) := do
  let i ← ls.findIdx? (·.startsWith "/-!")
  let j ← (ls.extract i ls.size).findIdx? (· == "-/")
  return (ls.extract 0 i, ls.extract i (i + j + 1), ls.extract (i + j + 1) ls.size)

/-- The text without the theorem `name`: from the docstring opening before `theorem name ` to the
next blank line, inclusive. -/
def dropTheorem (name : String) (ls : Array String) : Option (Array String) := do
  let t ← ls.findIdx? (·.startsWith s!"theorem {name} ")
  let d ← ((ls.extract 0 t).toList.reverse.findIdx? (·.startsWith "/--")).map (t - 1 - ·)
  let b := ((ls.extract t ls.size).findIdx? (· == "")).getD (ls.size - t)
  return ls.extract 0 d ++ ls.extract (t + b + 1) ls.size

/-- The compared theorem: the first entry of `theorem_names` in `comparator.json`, without the
namespace `FEEC.`. -/
def theoremName (json : String) : Option String :=
  match json.splitOn "\"theorem_names\": [\"FEEC." with
  | [_, rest] => (rest.splitOn "\"").head?
  | _ => none

/-- The expected `Defs.lean`: the imports and the body of the challenge (without the theorem)
around the module docstring of the current `Defs.lean`. -/
def expected (pkg : System.FilePath) (name chal cur : String) : Except String String := do
  let some (imps, _, body) := splitDoc (pyLines chal)
    | throw s!"{pkg / "Challenge.lean"}: no module docstring"
  let some (_, doc, _) := splitDoc (pyLines cur)
    | throw s!"{pkg / "Solution" / "Defs.lean"}: no module docstring"
  let some body := dropTheorem name body
    | throw s!"{pkg / "Challenge.lean"}: no `theorem {name}`"
  return "\n".intercalate (imps ++ doc ++ body).toList ++ "\n"

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

/-- The checks of one package. -/
def runPackage (pkg : System.FilePath) (write doBuild : Bool) (rep : Report) : IO Report := do
  let mut rep := rep
  let defs := pkg / "Solution" / "Defs.lean"
  let some name := theoremName (← readText (pkg / "comparator.json"))
    | return rep.addError s!"{pkg / "comparator.json"}: no theorem name `FEEC.…`"
  let cur ← readText defs
  match expected pkg name (← readText (pkg / "Challenge.lean")) cur with
  | .error e => rep := rep.addError e
  | .ok exp =>
    if exp != cur then
      if write then
        IO.FS.writeFile defs exp
        rep := rep.addInfo s!"Palomar: wrote {defs}"
      else
        rep := rep.addError s!"{defs}:1: not the definitions of {pkg / "Challenge.lean"}; \
          regenerate with `lake exe feec-palomar --write`"
  if doBuild then
    if let .error e ← build pkg then rep := rep.addError e
  return rep.addInfo s!"Palomar: {defs} against FEEC.{name} of {pkg / "Challenge.lean"}\
    {if doBuild then s!", lake build in {pkg}" else ""}"

def run (write : Bool := false) (doBuild : Bool := true) : IO Report := do
  let mut rep : Report := { name := "Palomar" }
  for pkg in packages do
    rep ← runPackage pkg write doBuild rep
  return rep.addInfo s!"Palomar: {packages.size} packages, {rep.errors.size} errors"

end FeecCheck.Palomar
