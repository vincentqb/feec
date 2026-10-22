import Lean

/-!
# The environment of `Feec`

The checks that look at declarations (axioms, names, docstrings) import `Feec` at run time from
the `.olean` files of `lake build Feec` (the executables declare `needs = ["Feec"]`, so `lake exe`
builds the library first). They do not link `Feec`: importing at run time keeps the executables
small and their build independent of the library.
-/

namespace FeecCheck

open Lean

private unsafe def loadFeecImpl (withChecks : Bool := false) : IO Environment := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let mods := if withChecks then #[`Feec, `FeecCheck] else #[`Feec]
  importModules (mods.map ({ module := · })) {} (loadExts := true)

/-- Import `Feec` (with environment extensions, as `lean` does for a file `import Feec`); with
`withChecks`, also the library `FeecCheck` of the gate (whose names the documentation cites). -/
@[implemented_by loadFeecImpl]
opaque loadFeec (withChecks : Bool := false) : IO Environment

/-- The module of a constant, if it was imported. -/
def moduleOf? (env : Environment) (nm : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? nm
  env.header.moduleNames[idx.toNat]?

/-- The constants defined in a `Feec.*` module, with their modules (read from the module data of
the `Feec.*` modules rather than by folding over the whole environment, which is much slower). -/
def feecConstants (env : Environment) : Array (Name × Name × ConstantInfo) := Id.run do
  let mut acc := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]
    unless (`Feec).isPrefixOf mod do continue
    let some data := env.header.moduleData[i]? | continue
    for nm in data.constNames do
      -- the module that owns the name (as `getModuleIdxFor?`), and the constant as the
      -- environment sees it
      if env.getModuleIdxFor? nm != some i then continue
      if let some ci := env.find? nm then acc := acc.push (nm, mod, ci)
  return acc

/-- `Feec.Foo.Bar` ↦ `Feec/Foo/Bar.lean`. -/
def pathOfModule (mod : Name) : String :=
  mod.toStringWithSep "/" (escape := false) ++ ".lean"

/-- Run a `CoreM` action on `env`. -/
def runCore {α : Type} (env : Environment) (x : CoreM α) (openDecls : List OpenDecl := []) :
    IO α := do
  let (a, _) ← x.toIO
    { fileName := "<FeecCheck>", fileMap := default, maxHeartbeats := 0, openDecls } { env }
  return a

/-- `path:line` of a declaration (line `1` when it has no recorded range). -/
def declLocation (env : Environment) (nm : Name) : IO String := do
  let some mod := moduleOf? env nm | return "<unknown>"
  let line ← runCore env do
    let r ← findDeclarationRanges? nm
    return (r.map (·.range.pos.line)).getD 1
  return s!"{pathOfModule mod}:{line}"

end FeecCheck
