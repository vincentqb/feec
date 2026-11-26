module

public import FeecCheck.Axioms
public import FeecCheck.Citations
public import FeecCheck.Layering
public import FeecCheck.Naming
public import FeecCheck.Palomar

/-!
# Command-line entry points

One function per executable of `lakefile.toml`; each prints its report(s) and returns the exit
code (`0` iff every check passed). `lake exe feec-gate` runs every check on one import of `Feec`:

| check | executable | needs `Feec` |
|---|---|---|
| citation convention | `feec-citations` | no |
| import layering | `feec-layering` | no |
| axiom audit | `feec-axioms` | yes |
| banned identifiers | `feec-naming` | yes |
| `palomar/*`: shared blocks canonical, `Defs.lean` copies the challenge, `lake build` | `feec-palomar` | no (builds every package) |

Run from the root of the repository (as `lake exe` does) after `lake build`; the executables that
import `Feec` declare `needs = ["Feec"]`, so `lake exe` builds the library first.
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

def mainPalomar (args : List String) : IO UInt32 := do
  unless args.all (fun a => a == "--write" || a == "--no-build") do
    return ← usage "lake exe feec-palomar [--write] [--no-build]"
  finish [← Palomar.run (write := args.contains "--write") (doBuild := !args.contains "--no-build")]

def mainGate : List String → IO UInt32
  | [] => do
    let mut rs := #[← Citations.run, ← Layering.run]
    let env ← loadFeec
    rs := rs.push (← Axioms.run env)
    rs := rs.push (← Naming.run env)
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
