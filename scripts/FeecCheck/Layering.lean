import FeecCheck.Util

/-!
# Layering gate

`lake exe feec-layering` (also run by `lake exe feec-gate`) checks the import rules of
`docs/REFACTOR_PLAN.md` §1 on the headers of `Feec/**/*.lean` (no environment needed).

The layers (the top-level directories of `Feec/`) form a partial order, not a chain: the table
`layerDeps` lists, for each layer, the layers it may import directly, and a layer may import a
module of layer `L'` iff `L'` is the layer itself, a layer of its `layerSiblings` group, or
reachable through `layerDeps` (the reflexive-transitive closure). Layers that no path joins
(`Fourier` and `Domain`; `Variational` and `TimeStepping`; `Examples` and `Numerics`; `Algebra`
and the analytic chain `Operator` → … → `HilbertComplex`) may not import each other. The relation
is the one drawn in `docs/REFACTOR_PLAN.md` §1; change both together.

The check fails when

* a module lives in a top-level directory that is not a layer of `layerDeps`;
* a module imports a module of a layer that its layer may not import, or the root module `Feec`;
* `Feec.lean` does not import every module of `Feec/`.

Before reading any file it checks the table itself against the hard rules of the plan (an error
here means the table was edited wrongly):

* the graph of `layerDeps`, with each `layerSiblings` group contracted to one node, has no cycle;
* `ForMathlib` and `Mesh` reach no other layer (they import only Mathlib and themselves);
* no layer below the top tier (`topTier`) reaches a layer of the top tier
  (`Models`, `Physics`, `Counterexamples`, `Examples`, `Numerics`, `Instances`), except as listed
  in `layerDeps` within the tier;
* no layer reaches `Instances` (only `Feec.lean` imports it).

Violations are reported at the import line, `path:line`.
-/

namespace FeecCheck.Layering

/-- The layers (top-level directories of `Feec/`) and the layers each may import directly
(`docs/REFACTOR_PLAN.md` §1). A layer may import the reflexive-transitive closure of its row
(see `Table.mayImport`). Edges that the plan documents individually:

* `Variational → Evolution`: the Galerkin error bound for evolution problems
  (`Feec.Variational.GalerkinEvolution`) uses the energy method of `Feec.Evolution.Energy`;
* `Fourier → Algebra`, `Domain → Algebra`: symbols and fibres of exterior algebra;
* `Geometry → Algebra`: the Levi-Civita symbol and metrics;
* `FiniteElement → Mesh`: finite elements live on simplicial meshes;
* `TimeStepping → Semigroup`: one-step schemes approximate semigroups (resolvents of m-dissipative
  generators, Taylor remainders of `e^{tL}`). -/
def layerDeps : List (String × List String) :=
  [("ForMathlib", []),
   ("Mesh", []),
   ("Algebra", ["ForMathlib"]),
   ("Geometry", ["Algebra"]),
   ("Operator", ["ForMathlib"]),
   ("Semigroup", ["Operator"]),
   ("Evolution", ["Semigroup"]),
   ("Variational", ["Evolution"]),
   ("TimeStepping", ["Semigroup"]),
   ("HilbertComplex", ["Variational"]),
   ("Fourier", ["HilbertComplex", "Algebra"]),
   ("Domain", ["HilbertComplex", "Algebra"]),
   ("FiniteElement", ["Domain", "Mesh"]),
   ("Models", ["FiniteElement", "Fourier", "Geometry", "TimeStepping"]),
   ("Physics", ["Models"]),
   ("Counterexamples", ["Models"]),
   ("Examples", ["Physics", "Counterexamples"]),
   ("Numerics", ["Physics", "Counterexamples"]),
   ("Instances", ["Examples", "Numerics"])]

/-- Groups of layers of one tier that may import each other freely (Lean keeps the modules
acyclic): the physical statements and the counterexamples use each other. -/
def layerSiblings : List (List String) := [["Physics", "Counterexamples"]]

/-- Layers that import no other part of `Feec` (only Mathlib and themselves). -/
def isolatedLayers : List String := ["ForMathlib", "Mesh"]

/-- The top tier: instances, applications and counterexamples. Nothing below imports them. -/
def topTier : List String :=
  ["Models", "Physics", "Counterexamples", "Examples", "Numerics", "Instances"]

/-- The relation of `docs/REFACTOR_PLAN.md` §1: direct edges, sibling groups, the layers that
import only Mathlib, and the top tier. -/
structure Table where
  deps : List (String × List String) := layerDeps
  siblings : List (List String) := layerSiblings
  isolated : List String := isolatedLayers
  top : List String := topTier

namespace Table

variable (t : Table)

def layerNames : List String := t.deps.map (·.1)

/-- The sibling group of a layer (the layer alone if it is in none). -/
def group (l : String) : List String := (t.siblings.find? (·.contains l)).getD [l]

/-- The direct edges of a layer, its siblings' edges included. -/
def edges (l : String) : List String :=
  (t.group l).flatMap fun m => (t.deps.lookup m).getD []

/-- The layers other than `l` reachable from `l` (`layerDeps` edges or sibling steps). -/
def reach (l : String) : List String := Id.run do
  let mut seen : List String := []
  let mut todo := (t.group l).filter (· != l) ++ t.edges l
  -- every step either shortens `todo` or adds a layer to `seen` (at most `n` times, each adding
  -- at most `n` entries to `todo`), so `(n + 1)²` steps suffice
  for _ in [0:(t.layerNames.length + 1) * (t.layerNames.length + 1)] do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      unless seen.contains m || m == l do
        seen := seen ++ [m]
        todo := todo ++ (t.group m).filter (· != m) ++ t.edges m
  return seen

/-- Whether a module of layer `l` may import a module of layer `l'`. -/
def mayImport (l l' : String) : Bool := l == l' || (t.reach l).contains l'

/-- Errors in the table itself (the hard rules of `docs/REFACTOR_PLAN.md` §1). -/
def errors : Array String := Id.run do
  let me := "scripts/FeecCheck/Layering.lean:1"
  let mut out := #[]
  for (l, ds) in t.deps do
    for d in ds do
      unless t.layerNames.contains d do out := out.push s!"{me}: deps: {l} → unknown layer {d}"
  for g in t.siblings do
    for l in g do
      unless t.layerNames.contains l do out := out.push s!"{me}: siblings: unknown layer {l}"
  for l in t.layerNames do
    -- a cycle through `l` that leaves its sibling group
    if (t.reach l).any (fun m => !(t.group l).contains m && (t.reach m).contains l) then
      out := out.push s!"{me}: the layer graph has a cycle through {l} (outside its sibling group)"
    if t.isolated.contains l && !(t.reach l).isEmpty then
      out := out.push s!"{me}: {l} must import only Mathlib, but reaches {t.reach l}"
    if !t.top.contains l then
      for m in t.reach l do
        if t.top.contains m then
          out := out.push s!"{me}: {l} is below the top tier but reaches {m}"
    if (t.reach l).contains "Instances" then
      out := out.push s!"{me}: {l} reaches Instances (only Feec.lean imports Instances)"
  return out

end Table

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

def run (t : Table := {}) : IO Report := do
  let mut rep : Report := { name := "Layering" }
  for e in t.errors do rep := rep.addError e
  let files ← leanFiles "Feec"
  let mut nimp := 0
  for f in files do
    let mod := moduleOfPath f
    let some l := layerOf mod | continue
    unless t.layerNames.contains l do
      rep := rep.addError s!"{f}:1: unknown layer Feec.{l}; add it to the table `layerDeps` of \
        scripts/FeecCheck/Layering.lean and to docs/REFACTOR_PLAN.md §1"
      continue
    for (k, m) in imports (← readText f) do
      nimp := nimp + 1
      let some l' := layerOf m | do
        if m == "Feec" then rep := rep.addError s!"{f}:{k}: imports the root module Feec"
        continue
      if !t.layerNames.contains l' then
        rep := rep.addError s!"{f}:{k}: import of {m} from the unknown layer Feec.{l'}"
      else if !t.mayImport l l' then
        let why := if t.isolated.contains l then s!"Feec.{l} imports only Mathlib"
          else s!"Feec.{l} may import only {(l :: t.reach l).map ("Feec." ++ ·)}"
        rep := rep.addError s!"{f}:{k}: layer violation: {why}, but this imports {m} \
          (docs/REFACTOR_PLAN.md §1)"
  -- `Feec.lean` imports every module
  let root ← imports <$> readText "Feec.lean"
  let rootMods : Std.HashSet String := root.foldl (fun s (_, m) => s.insert m) {}
  for f in files do
    unless rootMods.contains (moduleOfPath f) do
      rep := rep.addError s!"Feec.lean:1: does not import {moduleOfPath f} ({f})"
  return rep.addInfo s!"layering: {files.size} modules, {nimp} imports checked, \
    {t.layerNames.length} layers"

end FeecCheck.Layering
