module

public import FeecCheck.Util

/-!
# Palomar gate

`lake exe feec-palomar` (also run by `lake exe feec-gate`). Checks the Palomar submission
package `palomar/` (README, "Palomar submission"):

1. `palomar/Solution/Defs.lean` is the copy of the definitions of `palomar/Challenge.lean`: the
   same imports and, after the module docstring, the same text with the theorem `FEEC.feec`
   (its docstring, statement and proof, up to the next blank line) removed. The module docstring
   of `Defs.lean` is its own. `lake exe feec-palomar --write` regenerates `Defs.lean` from the
   challenge, keeping that docstring.
2. `lake build` in `palomar/` succeeds (the bridge `palomar/Solution/Bridge.lean` still compiles
   against `Feec`), with no warning but the `sorry` of `Challenge.lean`.

The comparator (`cd palomar && lake comparator`, several minutes) is not run here: it judges the
solution against the challenge before a submission.
-/

public section

namespace FeecCheck.Palomar

def challenge : System.FilePath := "palomar/Challenge.lean"
def defs : System.FilePath := "palomar/Solution/Defs.lean"

/-- The lines before the module docstring, the module docstring (`/-!` to the first line `-/`)
and the lines after it. -/
def splitDoc (ls : Array String) : Option (Array String × Array String × Array String) := do
  let i ← ls.findIdx? (·.startsWith "/-!")
  let j ← (ls.extract i ls.size).findIdx? (· == "-/")
  return (ls.extract 0 i, ls.extract i (i + j + 1), ls.extract (i + j + 1) ls.size)

/-- The text without the theorem `feec`: from the docstring opening before `theorem feec ` to the
next blank line, inclusive. -/
def dropTheorem (ls : Array String) : Option (Array String) := do
  let t ← ls.findIdx? (·.startsWith "theorem feec ")
  let d ← ((ls.extract 0 t).toList.reverse.findIdx? (·.startsWith "/--")).map (t - 1 - ·)
  let b := ((ls.extract t ls.size).findIdx? (· == "")).getD (ls.size - t)
  return ls.extract 0 d ++ ls.extract (t + b + 1) ls.size

/-- The expected `Defs.lean`: the imports and the body of the challenge (without the theorem)
around the module docstring of the current `Defs.lean`. -/
def expected (chal cur : String) : Except String String := do
  let some (imps, _, body) := splitDoc (pyLines chal) | throw s!"{challenge}: no module docstring"
  let some (_, doc, _) := splitDoc (pyLines cur) | throw s!"{defs}: no module docstring"
  let some body := dropTheorem body | throw s!"{challenge}: no `theorem feec`"
  return "\n".intercalate (imps ++ doc ++ body).toList ++ "\n"

/-- `lake build` in `palomar/`, outside the environment of the calling `lake exe`. -/
def build : IO (Except String Unit) := do
  let unset := #["LAKE", "LAKE_HOME", "LEAN_PATH", "LEAN_SRC_PATH"].map (·, none)
  let out ← IO.Process.output { cmd := "lake", args := #["build"], cwd := "palomar", env := unset }
  let log := out.stdout ++ out.stderr
  if out.exitCode != 0 then
    return .error s!"palomar: `lake build` failed (exit {out.exitCode}):\n{log}"
  let bad := (pyLines log).filter fun l => l.startsWith "warning:" &&
    !(l.startsWith "warning: Challenge.lean:" && l.endsWith "declaration uses `sorry`")
  unless bad.isEmpty do
    return .error s!"palomar: `lake build` warns:\n{"\n".intercalate bad.toList}"
  return .ok ()

def run (write : Bool := false) (doBuild : Bool := true) : IO Report := do
  let mut rep : Report := { name := "Palomar" }
  let cur ← readText defs
  match expected (← readText challenge) cur with
  | .error e => rep := rep.addError e
  | .ok exp =>
    if exp != cur then
      if write then
        IO.FS.writeFile defs exp
        rep := rep.addInfo s!"Palomar: wrote {defs}"
      else
        rep := rep.addError s!"{defs}:1: not the definitions of {challenge}; regenerate with \
          `lake exe feec-palomar --write`"
  if doBuild then
    if let .error e ← build then rep := rep.addError e
  return rep.addInfo s!"Palomar: {defs} against {challenge}\
    {if doBuild then ", lake build in palomar/" else ""}, {rep.errors.size} errors"

end FeecCheck.Palomar
