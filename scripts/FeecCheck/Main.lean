module

public import FeecCheck.Axioms
public import FeecCheck.Citations
public import FeecCheck.DocNames
public import FeecCheck.Layering
public import FeecCheck.MapCheck
public import FeecCheck.Naming
public import FeecCheck.Palomar
public import FeecCheck.Snapshot
public import FeecCheck.ThesisMap

/-!
# Command-line entry points

One function per executable of `lakefile.toml`; each prints its report(s) and returns the exit
code (`0` iff every check passed). `lake exe feec-gate` runs every check of the verification gate
of `docs/REFACTOR_PLAN.md` §5 on one import of `Feec` (and of `FeecCheck`, whose names the
documentation cites):

| check | executable | needs `Feec` |
|---|---|---|
| citation convention | `feec-citations` | no |
| import layering | `feec-layering` | no |
| axiom audit | `feec-axioms` | yes |
| banned identifiers | `feec-naming` | yes |
| `docs/THESIS_MAP.md` up to date | `feec-thesismap --check` | yes |
| migration coverage | `feec-mapcheck --strict` | yes |
| names in `README.md` and `docs/*.md` exist | `feec-docnames` | yes (and `FeecCheck`) |
| `palomar/{static,dynamic}`: `Defs.lean` copies the challenge, `lake build` | `feec-palomar` | no (builds both packages) |

Run from the root of the repository (as `lake exe` does) after `lake build`; the executables that
import `Feec` declare `needs = ["Feec"]` (`feec-gate` and `feec-docnames` also `"FeecCheck"`), so
`lake exe` builds the libraries first.
-/

public section

namespace FeecCheck

def finish (rs : List Report) : IO UInt32 := do
  for r in rs do r.print
  return if rs.all (·.ok) then 0 else 1

def usage (u : String) : IO UInt32 := do
  IO.eprintln s!"usage: {u}"
  return 2

def mainCitations : List String → IO UInt32
  | [] => do finish [← Citations.run]
  | ["--dump-bib"] => do
    match ← Citations.readBib with
    | .ok bib =>
      for (k, (a, t)) in bib.toArray.qsort (fun x y => x.1 < y.1) do IO.println s!"{k}\t{a}\t{t}"
      return 0
    | .error e => IO.eprintln e; return 1
  | _ => usage "lake exe feec-citations [--dump-bib]"

def mainLayering : List String → IO UInt32
  | [] => do finish [← Layering.run]
  | _ => usage "lake exe feec-layering"

def mainAxioms : List String → IO UInt32
  | [] => do finish [← Axioms.run (← loadFeec)]
  | _ => usage "lake exe feec-axioms"

def mainNaming : List String → IO UInt32
  | [] => do finish [← Naming.run (← loadFeec)]
  | _ => usage "lake exe feec-naming"

def mainThesisMap : List String → IO UInt32
  | [] => do finish [← ThesisMap.run (← loadFeec)]
  | ["--check"] => do finish [← ThesisMap.run (← loadFeec) (check := true)]
  | [out] => if out.startsWith "-" then usage "lake exe feec-thesismap [OUT | --check]"
    else do finish [← ThesisMap.run (← loadFeec) out]
  | _ => usage "lake exe feec-thesismap [OUT | --check]"

def mainMapCheck (args : List String) : IO UInt32 := do
  let u := "lake exe feec-mapcheck [--strict] [--no-env]"
  unless args.all (fun a => a == "--strict" || a == "--no-env" || a == "--no-lean") do
    return ← usage u
  let env? ← if args.any (fun a => a == "--no-env" || a == "--no-lean") then pure none
    else some <$> loadFeec
  finish [← MapCheck.run env? (args.contains "--strict")]

def mainDocNames : List String → IO UInt32
  | [] => do finish [← DocNames.run (← loadFeec (withChecks := true))]
  | _ => usage "lake exe feec-docnames"

def mainPalomar : List String → IO UInt32
  | [] => do finish [← Palomar.run]
  | ["--write"] => do finish [← Palomar.run (write := true)]
  | _ => usage "lake exe feec-palomar [--write]"

def mainSnapshot : List String → IO UInt32
  | [out] => if out.startsWith "-" then usage "lake exe feec-snapshot OUT" else do
    finish [← Snapshot.run (← loadFeec) out]
  | _ => usage "lake exe feec-snapshot OUT"

def mainGate : List String → IO UInt32
  | [] => do
    let mut rs := #[← Citations.run, ← Layering.run]
    let env ← loadFeec (withChecks := true)
    rs := rs.push (← Axioms.run env)
    rs := rs.push (← Naming.run env)
    rs := rs.push (← ThesisMap.run env (check := true))
    rs := rs.push (← MapCheck.run env true)
    rs := rs.push (← DocNames.run env)
    rs := rs.push (← Palomar.run)
    for r in rs do
      r.print
      IO.println ""
    let bad := rs.filter (!·.ok)
    if bad.isEmpty then
      IO.println s!"feec-gate: OK ({", ".intercalate (rs.toList.map (·.name))})"
      return 0
    IO.println s!"feec-gate: FAIL ({", ".intercalate (bad.toList.map (·.name))})"
    return 1
  | _ => usage "lake exe feec-gate"

end FeecCheck
