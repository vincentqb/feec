import Feec
open Lean Elab Command

/-!
# Axiom audit

`#audit_feec_axioms` checks every constant defined in a `Feec.*` module (any namespace,
including auxiliary and private declarations) and fails unless its axioms are among
`propext`, `Classical.choice`, `Quot.sound`. This rejects `sorryAx` (from `sorry`/`admit`),
`Lean.ofReduceBool`/`Lean.trustCompiler` (from `native_decide`) and any user `axiom`.

Run: `lake env lean scripts/AxiomAudit.lean` (after `lake build Feec`).
-/

elab "#audit_feec_axioms" : command => do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut n : Nat := 0
  for (nm, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? nm | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless (`Feec).isPrefixOf mod do continue
    n := n + 1
    let axs ← liftCoreM <| collectAxioms nm
    for a in axs do
      if !ok.contains a then bad := bad.push (nm, a)
  if bad.isEmpty then
    logInfo m!"axiom audit: clean ({n} Feec constants; only propext, Classical.choice, Quot.sound)"
  else
    throwError m!"axiom audit: {bad.size} non-standard axiom uses in {n} Feec constants: {bad.toList}"

#audit_feec_axioms
