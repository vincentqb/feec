import Feec
open Lean Elab Command

/-!
# Docstring dump

Writes `name \t docstring` (one line, tabs/newlines collapsed) for every declaration of a
`Feec.*` module that has a docstring, to the file named by `FEEC_DOCDUMP_OUT`
(default `/tmp/feec_docdump.tsv`). Used by `scripts/ThesisMap.sh`.
-/

def oneLineDoc (s : String) : String :=
  let s := s.map fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c
  " ".intercalate ((s.splitOn " ").filter (· ≠ ""))

elab "#dump_feec_docs" : command => do
  let env ← getEnv
  let out := (← IO.getEnv "FEEC_DOCDUMP_OUT").getD "/tmp/feec_docdump.tsv"
  let mut rows : Array String := #[]
  for (nm, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? nm | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless (`Feec).isPrefixOf mod do continue
    if nm.isInternal then continue
    let some doc ← findDocString? env nm | continue
    rows := rows.push s!"{nm}\t{mod}\t{oneLineDoc doc}"
  let sorted := rows.qsort (· < ·)
  IO.FS.writeFile out ("\n".intercalate sorted.toList ++ "\n")
  logInfo m!"wrote {sorted.size} docstrings to {out}"

#dump_feec_docs
