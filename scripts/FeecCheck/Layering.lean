import FeecCheck.Util

/-!
# Layering gate

`lake exe feec-layering` (also run by `lake exe feec-gate`) checks the import rules of
`docs/REFACTOR_PLAN.md` §1 on the headers of `Feec/**/*.lean` (no environment needed):

* every module lives in a known top-level directory (a *layer* of the table `layers`);
* a module imports only modules of its own layer or of lower layers. The order is
  `ForMathlib` < `Operator` < `Semigroup` < `Evolution` < `Variational`, `TimeStepping` <
  `HilbertComplex` < `Fourier`, `Domain`, `Algebra`, `Geometry`, `Mesh` < `FiniteElement` <
  `Models` < `Physics`, `Counterexamples` < `Numerics`, `Examples` < `Instances`; layers of one
  rank are siblings and may import each other (Lean keeps the modules acyclic). In particular
  nothing below `Models` imports `Models`, `Physics`, `Counterexamples` or `Instances`, and only
  `Feec.lean` imports `Instances`;
* `ForMathlib` and `Mesh` import no other part of `Feec` (only Mathlib and themselves);
* `Feec.lean` imports every module of `Feec/`.

Violations are reported at the import line, `path:line`.
-/

namespace FeecCheck.Layering

/-- Top-level directories of `Feec/` and their ranks. -/
def layers : List (String × Nat) :=
  [("ForMathlib", 0), ("Operator", 1), ("Semigroup", 2), ("Evolution", 3), ("Variational", 4),
   ("TimeStepping", 4), ("HilbertComplex", 5), ("Fourier", 6), ("Domain", 6), ("Algebra", 6),
   ("Geometry", 6), ("Mesh", 6), ("FiniteElement", 7), ("Models", 8), ("Physics", 9),
   ("Counterexamples", 9), ("Numerics", 10), ("Examples", 10), ("Instances", 11)]

/-- Layers that import no other part of `Feec`. -/
def isolated : List String := ["ForMathlib", "Mesh"]

/-- The imports of a header: `(line, module)` for each `[public] [meta] import [all] M₁ M₂ …`
line before the first command that is not an import (`module`, `prelude`, comments and blank lines
are skipped). -/
def imports (src : String) : Array (Nat × String) := Id.run do
  let mut out := #[]
  let mut inComment := false
  for (line, k) in (pyLines src).zipIdx do
    let t := pyStrip line
    if inComment then
      if (t.splitOn "-/").length > 1 then inComment := false
      continue
    if t.isEmpty || t.startsWith "--" || t == "module" || t == "prelude" then continue
    if t.startsWith "/-" && !t.startsWith "/-!" && !t.startsWith "/--" then
      if (t.splitOn "-/").length == 1 then inComment := true
      continue
    let ws := pyWords t
    let ws := ws.dropWhile (fun w => w == "public" || w == "private" || w == "meta")
    match ws with
    | "import" :: rest =>
      for m in rest.dropWhile (· == "all") do
        out := out.push (k + 1, m)
    | _ => break
  return out

/-- The layer of a module `Feec.L.…` (`none` for `Feec` itself or a non-`Feec` module). -/
def layerOf (mod : String) : Option String :=
  match mod.splitOn "." with
  | "Feec" :: l :: _ => some l
  | _ => none

def run : IO Report := do
  let mut rep : Report := { name := "Layering" }
  let files ← leanFiles "Feec"
  let mut nimp := 0
  for f in files do
    let mod := moduleOfPath f
    let some l := layerOf mod | continue
    let some r := layers.lookup l | do
      rep := rep.addError s!"{f}:1: unknown layer Feec.{l}; add it to the layer table of \
        scripts/FeecCheck/Layering.lean and docs/REFACTOR_PLAN.md §1"
      continue
    for (k, m) in imports (← readText f) do
      nimp := nimp + 1
      let some l' := layerOf m | do
        if m == "Feec" then rep := rep.addError s!"{f}:{k}: imports the root module Feec"
        continue
      if isolated.contains l && l' != l then
        rep := rep.addError s!"{f}:{k}: Feec.{l} imports only Mathlib, but this imports {m}"
        continue
      match layers.lookup l' with
      | none => rep := rep.addError s!"{f}:{k}: import of {m} from the unknown layer Feec.{l'}"
      | some r' =>
        if r' > r then
          rep := rep.addError s!"{f}:{k}: layer violation: Feec.{l} (rank {r}) imports {m} \
            (Feec.{l'}, rank {r'})"
  -- `Feec.lean` imports every module
  let root ← imports <$> readText "Feec.lean"
  let rootMods : Std.HashSet String := root.foldl (fun s (_, m) => s.insert m) {}
  for f in files do
    unless rootMods.contains (moduleOfPath f) do
      rep := rep.addError s!"Feec.lean:1: does not import {moduleOfPath f} ({f})"
  return rep.addInfo s!"layering: {files.size} modules, {nimp} imports checked"

end FeecCheck.Layering
