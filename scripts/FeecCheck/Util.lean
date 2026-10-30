module

public import FeecCheck.Regex
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Shared helpers of the gate checks

Reading the sources of the repository (with Python's universal-newline translation), listing the
Lean files of `Feec/`, line numbers, and a few string functions with Python's semantics.

Every check runs from the root of the repository (`lake exe` does), returns a `Report` (the
`path:line: message` errors and informational lines) and never throws on a violation.
-/

public section

namespace FeecCheck

/-- The outcome of one check. -/
structure Report where
  name : String
  /-- Informational lines (counts, notes). -/
  info : Array String := #[]
  /-- Violations, each `path:line: message` (or `path: message`). -/
  errors : Array String := #[]

namespace Report

def ok (r : Report) : Bool := r.errors.isEmpty

def addInfo (r : Report) (s : String) : Report := { r with info := r.info.push s }
def addError (r : Report) (s : String) : Report := { r with errors := r.errors.push s }

/-- Print the report; errors go to stdout as `path:line: message` lines (one per line). -/
def print (r : Report) : IO Unit := do
  for s in r.info do IO.println s
  for e in r.errors do IO.println e
  let n := r.errors.size
  IO.println s!"{r.name}: {if r.ok then "OK" else s!"FAIL ({n} error{if n == 1 then "" else "s"})"}"

end Report

/-- Read a text file as Python's `open(..., encoding='utf-8').read()` does (universal newlines:
`\r\n` and `\r` become `\n`). -/
def readText (p : System.FilePath) : IO String := do
  let s ← IO.FS.readFile p
  if s.contains '\r' then
    return (s.replace "\r\n" "\n").replace "\r" "\n"
  else return s

/-- The lines of a text, without their `\n` (Python's `for line in open(...)` followed by
`line.rstrip('\n')`; no final empty line for a trailing `\n`). -/
def pyLines (s : String) : Array String :=
  let ls := (s.splitOn "\n").toArray
  if s.endsWith "\n" then ls.pop else ls

def chars (s : String) : Array Char := s.toList.toArray

def ofChars (cs : Array Char) (a : Nat := 0) (b : Nat := cs.size) : String :=
  String.ofList (cs.extract a b).toList

/-- 1-based line of position `i` (Python's `s.count('\n', 0, i) + 1`). -/
def lineOf (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut n := 1
  for j in [0:min i cs.size] do
    if cs[j]! == '\n' then n := n + 1
  return n

/-- Python's `s.find(sub, start, end)` on characters; `none` for `-1`. -/
def findFrom (cs : Array Char) (sub : String) (start : Nat) (stop : Nat := cs.size) :
    Option Nat := Id.run do
  let p := chars sub
  if p.size > stop then return none
  let mut i := start
  while i + p.size ≤ stop do
    let mut okk := true
    for j in [0:p.size] do
      if cs[i + j]! != p[j]! then
        okk := false
        break
    if okk then return some i
    i := i + 1
  return none

/-- Python's `s.split()` (on runs of Unicode whitespace). -/
def pyWords (s : String) : List String :=
  (s.split isPySpace).toList.map (·.toString) |>.filter (· ≠ "")

/-- Python's `s.strip()`. -/
def pyStrip (s : String) : String :=
  String.ofList ((s.toList.dropWhile isPySpace).reverse.dropWhile isPySpace).reverse

/-- Python's `repr` of a string (single quotes; enough for the messages of the checks). -/
def pyRepr (s : String) : String :=
  "'" ++ (s.replace "\\" "\\\\").replace "'" "\\'" ++ "'"

/-- Python's `repr` of a list of strings. -/
def pyReprList (l : List String) : String :=
  "[" ++ ", ".intercalate (l.map pyRepr) ++ "]"

/-- The Lean files under `dir`, sorted (Python's `sorted(pathlib.Path(dir).rglob('*.lean'))`). -/
def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let fs ← dir.walkDir
  let fs := fs.filter fun f => f.extension == some "lean"
  let mut out := #[]
  for f in fs do
    if !(← f.isDir) then out := out.push f
  return out.qsort (·.toString < ·.toString)

/-- `Feec/Foo/Bar.lean` ↦ `Feec.Foo.Bar`. -/
def moduleOfPath (f : System.FilePath) : String :=
  ".".intercalate ((f.withExtension "").components)

/-- The relative path from the directory of `f` (a path relative to the repository root) to
`target` (also relative to the root): `os.path.relpath(target, f.parent)`. -/
def relPathFrom (f : System.FilePath) (target : String) : String :=
  let depth := (f.components.dropLast.filter (· ≠ ".")).length
  String.join (List.replicate depth "../") ++ target

/-- Insertion-ordered set of strings. -/
structure OrdSet where
  arr : Array String := #[]
  set : Std.HashSet String := {}

namespace OrdSet

def insert (s : OrdSet) (x : String) : OrdSet :=
  if s.set.contains x then s else ⟨s.arr.push x, s.set.insert x⟩

def contains (s : OrdSet) (x : String) : Bool := s.set.contains x

def size (s : OrdSet) : Nat := s.arr.size

end OrdSet

/-- Insertion-ordered map of strings to sets of strings (Python's `defaultdict(set)`). -/
structure SetMap where
  keys : OrdSet := {}
  map : Std.HashMap String (Std.HashSet String) := {}

namespace SetMap

def add (m : SetMap) (k v : String) : SetMap :=
  ⟨m.keys.insert k, m.map.insert k ((m.map.getD k {}).insert v)⟩

/-- Create the key with an empty set (the side effect of `d[k]` on a `defaultdict`). -/
def touch (m : SetMap) (k : String) : SetMap :=
  if m.keys.contains k then m else ⟨m.keys.insert k, m.map.insert k {}⟩

def addAll (m : SetMap) (k : String) (vs : Std.HashSet String) : SetMap :=
  vs.fold (fun m v => m.add k v) (m.touch k)

def get (m : SetMap) (k : String) : Std.HashSet String := m.map.getD k {}

def sorted (m : SetMap) (k : String) : Array String := (m.get k).toArray.qsort (· < ·)

/-- The union of all values. -/
def union (m : SetMap) : Std.HashSet String :=
  m.map.fold (fun acc _ v => v.fold (fun a x => a.insert x) acc) {}

end SetMap

end FeecCheck
