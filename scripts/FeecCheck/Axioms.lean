import FeecCheck.Util
import FeecCheck.Env

/-!
# Axiom audit

`lake exe feec-axioms` (also run by `lake exe feec-gate`) checks every constant defined in a
`Feec.*` module (any namespace, including auxiliary and private declarations) and fails unless its
axioms are among `propext`, `Classical.choice`, `Quot.sound`. This rejects `sorryAx` (from
`sorry`/`admit`), `Lean.ofReduceBool`/`Lean.trustCompiler` (from `native_decide`) and any user
`axiom`. Each offending constant is reported at its declaration, `path:line`.
-/

namespace FeecCheck.Axioms

open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def run (env : Environment) : IO Report := do
  let cs := feecConstants env
  let bad ← runCore env do
    let mut bad : Array (Name × Array Name) := #[]
    for (nm, _, _) in cs do
      let axs ← collectAxioms nm
      let axs := axs.filter (!allowed.contains ·)
      unless axs.isEmpty do bad := bad.push (nm, axs)
    return bad
  let mut rep : Report := { name := "AxiomAudit" }
  for (nm, axs) in bad.qsort (fun a b => a.1.toString < b.1.toString) do
    rep := rep.addError s!"{← declLocation env nm}: {nm} depends on the axioms {axs.toList}"
  return rep.addInfo s!"axiom audit: {cs.size} Feec constants, {bad.size} with non-standard \
    axioms (allowed: propext, Classical.choice, Quot.sound)"

end FeecCheck.Axioms
