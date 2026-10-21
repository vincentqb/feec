import FeecCheck.Util
import FeecCheck.Env

/-!
# Naming gate

`lake exe feec-naming` (also run by `lake exe feec-gate`) checks the identifiers of the library
against the bans of `docs/REFACTOR_PLAN.md` §1 and §5: every component of every declaration name
of a `Feec.*` module (namespaces included; private names are checked under their user-facing
name) and every component of every module name. Docstrings and comments are not checked: thesis
references belong there (`[QuennevilleBelair2015], Prop 4.17`).

Banned (see `rules`):
* thesis numbers: `prop_4_17`, `thm43`, `lemma_5_2`, `ch6_…`, `Ch4`, `Sol61`, `Hyp54`, `Sys56`,
  `C55`;
* process suffixes: `_unconditional`, `_of_isSkewAdjoint`, `_ambient`, `_literal`, `_corrected`,
  `_compr` (as a `_`-separated word). The plan also lists `_res` and `_max`; they are not checked,
  since `res` (a resolvent, a restriction) and `max` are ordinary Mathlib vocabulary
  (`Feec.Stone.res`, `Feec.Operator.mul_le_max_one`);
* thesis typography: `bigAL`, `tst`, `nV2`, `opMh`, `Bthesis`, `Complex3`;
* `Repair`, `Thesis`.

Each hit is reported at the declaration, `path:line` (module names at line 1).
-/

namespace FeecCheck.Naming

open Lean Re

/-- `word` as a `_`-separated word of a component: `(^|_)word(_|$)`. -/
def underscoreWord (w : String) : Re :=
  seqs [.alt .bos (chr '_'), lit w, .alt .eos (chr '_')]

/-- The banned patterns of a name component, with their descriptions. -/
def rules : List (String × Re) :=
  [("thesis number (thm/prop/cor/lemma N)",
      seqs [.alt .bos (chr '_'), lits ["thm", "prop", "cor", "lemma"], opt (chr '_'), digit]),
   ("thesis chapter (chN_)", seqs [.alt .bos (chr '_'), lit "ch", plus digit, chr '_']),
   ("thesis chapter (ChN)", seqs [lit "Ch", digit]),
   ("thesis label (Sol61/Hyp54/Sys56/C55)",
      seqs [.bos, lits ["Sol", "Hyp", "Sys", "C"], digit, digit, opt digit, .eos])] ++
  (["unconditional", "ambient", "literal", "corrected", "compr"].map fun w =>
    (s!"process suffix _{w}", underscoreWord w)) ++
  [("process suffix _of_isSkewAdjoint", seqs [lit "_of_isSkewAdjoint", .alt .eos (chr '_')])] ++
  (["bigAL", "tst", "nV2", "opMh", "Bthesis", "Complex3", "Repair", "Thesis"].map fun w =>
    (s!"thesis identifier {w}", lit w))

/-- The rules a component violates. -/
def violations (comp : String) : List String :=
  let cs := chars comp
  rules.filterMap fun (d, r) => if (r.search cs).isSome then some d else none

/-- The string components of a name (numeric components are skipped). -/
def strComponents (n : Name) : List String :=
  n.components.filterMap fun
    | .str _ s => some s
    | _ => none

def run (env : Environment) : IO Report := do
  let mut rep : Report := { name := "Naming" }
  -- module names
  let files ← leanFiles "Feec"
  for f in files do
    for c in (moduleOfPath f).splitOn "." do
      for d in violations c do
        rep := rep.addError s!"{f}:1: module name component {c}: {d}"
  -- declaration names
  let cs := feecConstants env
  let mut seen : Std.HashSet Name := {}
  let mut hits : Array (Name × String × String) := #[]
  for (nm, _, _) in cs do
    let user := (privateToUserName? nm).getD nm
    for c in strComponents user do
      for d in violations c do
        hits := hits.push (nm, c, d)
  for (nm, c, d) in hits.qsort (fun a b => a.1.toString < b.1.toString) do
    if seen.contains nm then continue
    seen := seen.insert nm
    rep := rep.addError s!"{← declLocation env nm}: {(privateToUserName? nm).getD nm}: \
      component {c}: {d}"
  return rep.addInfo s!"naming: {files.size} modules, {cs.size} declarations checked"

end FeecCheck.Naming
