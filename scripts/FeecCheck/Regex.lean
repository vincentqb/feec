module

/-!
# A small backtracking regular-expression engine

The gate checks of `FeecCheck` were first written as Python scripts around `re`. Lean core has no
regular expressions, so this module provides the fragment those scripts used, with Python's
semantics: leftmost match, greedy backtracking quantifiers, numbered groups, lookahead, the
anchors `^`/`$` (multiline) and `\A`/`\Z`, and the word boundary `\b`. Patterns are built with the
combinators below rather than parsed from a string.

Character classes follow Python's Unicode `str` semantics where the checks depend on them:
`\d` is `str.isdecimal`, `\s` is `str.isspace`, and `\w` is `str.isalnum() or '_'` for the scripts
and blocks that occur in the library (Latin, Greek, Cyrillic, IPA and phonetic modifiers, super- and
subscripts, letterlike symbols, number forms, mathematical alphanumerics).
-/

public section

namespace FeecCheck

/-- Python's `str.isspace`. -/
def isPySpace (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || (0x1c ≤ n && n ≤ 0x20) || n == 0x85 || n == 0xa0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200a) || n == 0x2028 || n == 0x2029 || n == 0x202f || n == 0x205f ||
    n == 0x3000

/-- Python's `str.isdecimal` (ASCII, Arabic-Indic, Devanagari, fullwidth and mathematical
digits). -/
def isPyDigit (c : Char) : Bool :=
  let n := c.toNat
  ('0'.toNat ≤ n && n ≤ '9'.toNat) || (0x660 ≤ n && n ≤ 0x669) || (0x6f0 ≤ n && n ≤ 0x6f9) ||
    (0x966 ≤ n && n ≤ 0x96f) || (0xff10 ≤ n && n ≤ 0xff19) || (0x1d7ce ≤ n && n ≤ 0x1d7ff)

/-- The value of a digit accepted by `isPyDigit` (Python's `int`). -/
def pyDigitVal (c : Char) : Nat :=
  let n := c.toNat
  if n ≤ '9'.toNat then n - '0'.toNat
  else if n ≤ 0x669 then n - 0x660
  else if n ≤ 0x6f9 then n - 0x6f0
  else if n ≤ 0x96f then n - 0x966
  else if n ≤ 0xff19 then n - 0xff10
  else (n - 0x1d7ce) % 10

/-- Python's `int` on a string of `isPyDigit` characters. -/
def pyInt (s : String) : Nat :=
  s.foldl (fun acc c => 10 * acc + pyDigitVal c) 0

private def inRanges (n : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (a, b) :: rs => (a ≤ n && n ≤ b) || inRanges n rs

/-- Python's `\w`: `str.isalnum()` or `_` (see the module docstring for the blocks covered). -/
def isPyWord (c : Char) : Bool :=
  let n := c.toNat
  if n < 128 then c.isAlphanum || c == '_'
  else
    n != 0xd7 && n != 0xf7 && n != 0x375 && n != 0x37e && n != 0x384 && n != 0x385 &&
      n != 0x387 && n != 0x3f6 && n != 0x2118 && n != 0x212e &&
    inRanges n [(0xaa, 0xaa), (0xb2, 0xb3), (0xb5, 0xb5), (0xb9, 0xba), (0xbc, 0xbe),
      (0xc0, 0x2c1), (0x2c6, 0x2d1), (0x2e0, 0x2e4), (0x2ec, 0x2ec), (0x2ee, 0x2ee),
      (0x370, 0x374), (0x376, 0x377), (0x37a, 0x37d), (0x37f, 0x37f), (0x386, 0x3ff),
      (0x400, 0x481), (0x48a, 0x52f), (0x531, 0x556), (0x561, 0x587), (0x5d0, 0x5ea),
      (0x620, 0x64a), (0x660, 0x669), (0x1401, 0x166c), (0x1d00, 0x1dbf), (0x1e00, 0x1fbc),
      (0x1fc2, 0x1fcc), (0x1fd0, 0x1fdb), (0x1fe0, 0x1fec), (0x1ff2, 0x1ffc),
      (0x2070, 0x2071), (0x2074, 0x2079), (0x207f, 0x2089), (0x2090, 0x209c),
      (0x2102, 0x2102), (0x2107, 0x2107), (0x210a, 0x2113), (0x2115, 0x2115),
      (0x2119, 0x211d), (0x2124, 0x2124), (0x2126, 0x2126), (0x2128, 0x2128),
      (0x212a, 0x212d), (0x212f, 0x2139), (0x213c, 0x213f), (0x2145, 0x2149),
      (0x214e, 0x214e), (0x2150, 0x2189), (0x2460, 0x249b), (0x24ea, 0x24ff),
      (0x2c00, 0x2cff), (0x3005, 0x3007), (0x3041, 0x30ff), (0x4e00, 0x9fff),
      (0xa640, 0xa69d), (0xa722, 0xa7ff), (0xff10, 0xff19), (0xff21, 0xff3a), (0xff41, 0xff5a),
      (0x1d400, 0x1d7ff)]

/-- A regular expression (abstract syntax). -/
inductive Re where
  /-- One character satisfying the predicate. -/
  | cls (p : Char → Bool)
  | seq (a b : Re)
  /-- Alternation; the left branch is tried first. -/
  | alt (a b : Re)
  /-- Greedy Kleene star. -/
  | star (a : Re)
  /-- Numbered capturing group (`1 ≤ i < 10`). -/
  | group (i : Nat) (a : Re)
  /-- Lookahead `(?=a)` (`neg = false`) or `(?!a)` (`neg = true`). -/
  | look (neg : Bool) (a : Re)
  /-- `^` with `re.M`: start of the string or after `\n`. -/
  | bol
  /-- `$` with `re.M`: end of the string or before `\n`. -/
  | eol
  /-- `\A`, and `^` without `re.M`. -/
  | bos
  /-- `\Z`. -/
  | eos
  /-- `\b`. -/
  | wordB
  | eps
deriving Inhabited

namespace Re

def chr (c : Char) : Re := .cls (· == c)
def lit (s : String) : Re := s.toList.foldr (fun c r => .seq (chr c) r) .eps
def seqs : List Re → Re
  | [] => .eps
  | [a] => a
  | a :: as => .seq a (seqs as)
def alts : List Re → Re
  | [] => .cls fun _ => false
  | [a] => a
  | a :: as => .alt a (alts as)
def lits (ss : List String) : Re := alts (ss.map lit)
def opt (a : Re) : Re := .alt a .eps
def plus (a : Re) : Re := .seq a (.star a)
def rep (n : Nat) (a : Re) : Re := seqs (List.replicate n a)
/-- `[^cs]`. -/
def noneOf (cs : List Char) : Re := .cls fun c => !cs.contains c
def oneOf (cs : List Char) : Re := .cls fun c => cs.contains c
/-- `\d`. -/
def digit : Re := .cls isPyDigit
/-- `\s`. -/
def space : Re := .cls isPySpace
/-- `\S`. -/
def nonSpace : Re := .cls fun c => !isPySpace c
/-- `\w`. -/
def word : Re := .cls isPyWord
/-- `.` (no `re.S`). -/
def any : Re := .cls (· != '\n')
def upper : Re := .cls fun c => 'A' ≤ c && c ≤ 'Z'
def lowerAZ : Re := .cls fun c => 'a' ≤ c && c ≤ 'z'
def alphaAZ : Re := .cls fun c => ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

end Re

/-- Captures: `caps[i] = some (start, stop)` for each group `i` that participated. -/
abbrev Caps := Array (Option (Nat × Nat))

/-- The input of a match: the characters and the end position (`endpos`). -/
structure Input where
  s : Array Char
  stop : Nat

private def Input.at (inp : Input) (i : Nat) : Char := inp.s[i]!

/-- Continuation-passing backtracking matcher. -/
partial def Re.go (inp : Input) : Re → Nat → Caps → (Nat → Caps → Option (Nat × Caps)) →
    Option (Nat × Caps)
  | .cls p, i, c, k => if i < inp.stop && p (inp.at i) then k (i + 1) c else none
  | .seq a b, i, c, k => a.go inp i c fun j c' => b.go inp j c' k
  | .alt a b, i, c, k =>
    match a.go inp i c k with
    | some r => some r
    | none => b.go inp i c k
  | .star a, i, c, k =>
    match a.go inp i c (fun j c' => if j == i then none else (Re.star a).go inp j c' k) with
    | some r => some r
    | none => k i c
  | .group g a, i, c, k => a.go inp i c fun j c' => k j (c'.set! g (some (i, j)))
  | .look neg a, i, c, k =>
    match a.go inp i c (fun j c' => some (j, c')), neg with
    | some _, true => none
    | none, true => k i c
    | some (_, c'), false => k i c'
    | none, false => none
  | .bol, i, c, k => if i == 0 || inp.at (i - 1) == '\n' then k i c else none
  | .eol, i, c, k => if i == inp.stop || inp.at i == '\n' then k i c else none
  | .bos, i, c, k => if i == 0 then k i c else none
  | .eos, i, c, k => if i == inp.stop then k i c else none
  | .wordB, i, c, k =>
    let a := i > 0 && isPyWord (inp.at (i - 1))
    let b := i < inp.stop && isPyWord (inp.at i)
    if a != b then k i c else none
  | .eps, i, c, k => k i c

/-- A match: the whole span and the groups. -/
structure Match where
  src : Array Char
  start : Nat
  stop : Nat
  caps : Caps

namespace Match

def span (m : Match) (i : Nat) : Option (Nat × Nat) :=
  if i == 0 then some (m.start, m.stop) else (m.caps[i]?).join

/-- Group `i` (`0` is the whole match), `none` if it did not participate. -/
def group? (m : Match) (i : Nat) : Option String :=
  (m.span i).map fun (a, b) => String.ofList (m.src.extract a b).toList

/-- Group `i`, `""` if it did not participate. -/
def group (m : Match) (i : Nat) : String := (m.group? i).getD ""

end Match

namespace Re

/-- Try to match `r` at position `i` (Python's `pattern.match(s, i, stop)`). -/
def matchAt (r : Re) (s : Array Char) (i : Nat) (stop : Nat := s.size) : Option Match :=
  let inp : Input := ⟨s, stop⟩
  (r.go inp i (Array.replicate 10 none) fun j c => some (j, c)).map fun (j, c) => ⟨s, i, j, c⟩

/-- Python's `pattern.finditer(s, pos, endpos)`. -/
def findAll (r : Re) (s : Array Char) (pos : Nat := 0) (stop : Nat := s.size) : Array Match :=
  Id.run do
    let mut out := #[]
    let mut i := pos
    let mut fuel := stop + 1 - pos
    while fuel > 0 && i ≤ stop do
      fuel := fuel - 1
      match r.matchAt s i stop with
      | some m =>
        out := out.push m
        i := if m.stop == i then i + 1 else m.stop
        fuel := stop + 1 - i
      | none => i := i + 1
    return out

/-- Python's `pattern.search(s)`. -/
def search (r : Re) (s : Array Char) (pos : Nat := 0) (stop : Nat := s.size) : Option Match :=
  Id.run do
    let mut i := pos
    while i ≤ stop do
      if let some m := r.matchAt s i stop then return some m
      i := i + 1
    return none

/-- Python's `pattern.fullmatch(s)`. -/
def fullMatch (r : Re) (s : String) : Option Match :=
  (Re.seq r .eos).matchAt s.toList.toArray 0

/-- `pattern.findall(s)` for a pattern with exactly one group: the texts of group `g`. -/
def findAllGroup (r : Re) (s : Array Char) (g : Nat := 1) : Array String :=
  (r.findAll s).map (·.group g)

/-- Python's `pattern.split(s)`: the pieces between matches, each followed by the texts of the
groups `groups` of the separating match. -/
def split (r : Re) (s : String) (groups : List Nat := []) : Array String := Id.run do
  let cs := s.toList.toArray
  let mut out := #[]
  let mut prev := 0
  for m in r.findAll cs do
    out := out.push (String.ofList (cs.extract prev m.start).toList)
    for g in groups do out := out.push (m.group g)
    prev := m.stop
  out.push (String.ofList (cs.extract prev cs.size).toList)

/-- Python's `pattern.sub(f, s)`. -/
def sub {m : Type → Type} [Monad m] (r : Re) (s : Array Char) (f : Match → m String) :
    m (Array Char) := do
  let mut out : Array Char := #[]
  let mut prev := 0
  for mt in r.findAll s do
    out := out ++ s.extract prev mt.start
    out := out ++ (← f mt).toList.toArray
    prev := mt.stop
  return out ++ s.extract prev s.size

end Re

end FeecCheck
