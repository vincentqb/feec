import FeecCheck.Util

/-!
# Citation gate

`lake exe feec-citations` (also run by `lake exe feec-gate`). Checks every Lean file of the library
(`Feec.lean` and `Feec/**/*.lean`):

1. every bracketed citation key `[Key]` (Key = AuthorYear, e.g. `[QuennevilleBelair2015]`,
   `[AFW2010]`) has an entry in `docs/references.bib`;
2. no citation carries its location inside the brackets (`[Key, Prop 4.17]`): doc-gen4 reads the
   whole bracket as the key, so the location goes outside, `[Key], Prop 4.17`;
3. no `Thesis:` tag (retired; thesis traceability is `[QuennevilleBelair2015], Prop 4.17`);
4. every module docstring has a `## References` section, and every key cited anywhere in the file
   has an entry there of the form `* [Author(s), *Title*][Key]` (optionally followed by a
   location), with the authors (initials and last names) and the title of `docs/references.bib`;
5. every module docstring declares its bibliography on a line of its own,
   `Bibliography: [references.bib](<path>)`, with `<path>` the relative path from the file to
   `docs/references.bib`, so that leantex (and doc-gen4) resolve the citations.

Each failure is reported as `path:line: message`.

The BibTeX reader is the small subset `docs/references.bib` uses: `@type{key,` entries, braced
`author`/`title` fields, `and`-separated `Last, First` (or `Last, Jr, First`) names, the accents
`\'`, `\"`, `` \` ``, `\v` and the math titles `{$L^2$}`, `{$L_2$}`.
-/

namespace FeecCheck.Citations

open Re

/-- `[A-Z][A-Za-z\-]*\d{4}[a-z]?`. -/
def key : Re := seqs [upper, .star (.alt alphaAZ (chr '-')), rep 4 digit, opt lowerAZ]

private def accentTable : List (String × List (Char × Char)) :=
  [("\\'", [('e', 'é'), ('a', 'á'), ('E', 'É'), ('o', 'ó'), ('i', 'í')]),
   ("\\\"", [('u', 'ü'), ('o', 'ö'), ('a', 'ä')]),
   ("\\`", [('e', 'è'), ('a', 'à')]),
   ("\\v", [('s', 'š'), ('c', 'č'), ('C', 'Č'), ('r', 'ř'), ('z', 'ž')])]

private def accent (m : Match) : Except String String := do
  let some tbl := accentTable.lookup (m.group 1) | throw s!"unknown accent {m.group 1}"
  let some c := (m.group 2).toList.head? | throw "empty accent argument"
  let some r := tbl.lookup c | throw s!"unknown accented letter {m.group 1}{c}"
  return r.toString

/-- `\\['"`]`. -/
private def accCmd : Re := seqs [chr '\\', oneOf ['\'', '"', '`']]

/-- `\{(\\['"`]|\\v)\{?([A-Za-z])\}?\}`. -/
private def accBraced : Re :=
  seqs [chr '{', .group 1 (.alt accCmd (lit "\\v")), opt (chr '{'), .group 2 alphaAZ,
    opt (chr '}'), chr '}']

/-- `(\\['"`])\{?([A-Za-z])\}?`. -/
private def accBare : Re := seqs [.group 1 accCmd, opt (chr '{'), .group 2 alphaAZ, opt (chr '}')]

/-- LaTeX to the text displayed in `## References`. -/
def delatex (s : String) : Except String String := do
  let s := (s.replace "{$L^2$}" "L²").replace "{$L_2$}" "L₂"
  let s ← accBraced.sub (chars s) accent
  let s ← accBare.sub s accent
  let s := (((String.ofList s.toList).replace "--" "–").replace "{" "").replace "}" ""
  return " ".intercalate (pyWords s)

/-- The braced value of field `name` of an entry body (first `\bname\s*=\s*\{`). -/
def field (body : Array Char) (name : String) : Except String String := do
  let r := seqs [.wordB, lit name, .star space, chr '=', .star space, chr '{']
  let some m := r.search body | return ""
  let i := m.stop
  let mut j := i
  let mut d : Int := 1
  while d != 0 do
    let some c := body[j]? | throw s!"unbalanced braces in field {name}"
    if c == '{' then d := d + 1
    if c == '}' then d := d - 1
    j := j + 1
  return ofChars body i (j - 1)

/-- `B. C.-D. Smith` style initials of the first names. -/
def initials (first : String) : Except String String := do
  let ws ← (pyWords first).mapM fun w => do
    if w.endsWith "." && w.length ≤ 3 then return w
    let ps ← (w.splitOn "-").mapM fun p => do
      let some c := p.toList.head? | throw s!"empty name part in {w}"
      return s!"{c}."
    return "-".intercalate ps
  return " ".intercalate ws

/-- `Last, First` or `Last, Jr, First` ↦ `F. Last` or `F. Last, Jr`. -/
def person (a : String) : Except String String := do
  let p := (a.splitOn ",").map pyStrip
  match p with
  | [last, jr, first] => return s!"{← initials first} {last}, {jr}"
  | last :: first :: _ => return s!"{← initials first} {last}"
  | _ => throw s!"author {pyRepr a} is not `Last, First`"

/-- `docs/references.bib`: key ↦ (authors, title) as displayed in `## References`, and the keys
in order of appearance. -/
def readBib (path : System.FilePath := "docs/references.bib") :
    IO (Except String (Std.HashMap String (String × String))) := do
  let src := chars (← readText path)
  let entry := seqs [chr '@', .group 1 (plus word), chr '{',
    .group 2 (plus (.cls fun c => c != ',' && !isPySpace c)), chr ',']
  let andSep := seqs [plus space, lit "and", plus space]
  return do
    let mut bib : Std.HashMap String (String × String) := {}
    for m in entry.findAll src do
      let nxt := (findFrom src "\n@" m.stop).getD src.size
      let body := src.extract m.stop nxt
      let au ← delatex (← field body "author")
      let authors ← if au.isEmpty then pure "" else do
        let ps ← (andSep.split au).toList.mapM person
        pure (", ".intercalate ps)
      bib := bib.insert (m.group 2) (authors, ← delatex (← field body "title"))
    return bib

def run : IO Report := do
  let mut rep : Report := { name := "CheckCitations" }
  let bib ← match ← readBib with
    | .ok b => pure b
    | .error e => return rep.addError s!"docs/references.bib: {e}"
  let cite := seqs [chr '[', .group 1 key, chr ']', .look true (chr '(')]
  let inside := seqs [chr '[', .group 1 key, chr ',']
  let thesis := seqs [.wordB, lit "Thesis:"]
  -- `^\* \[([^\[\]]*), \*([^*]+)\*\]\[(KEY)\]` (multiline)
  let entry := seqs [.bol, lit "* [", .group 1 (.star (noneOf ['[', ']'])), lit ", *",
    .group 2 (plus (noneOf ['*'])), lit "*][", .group 3 key, chr ']']
  let files := #[("Feec.lean" : System.FilePath)] ++ (← leanFiles "Feec")
  for f in files do
    let s := chars (← readText f)
    for m in cite.findAll s do
      unless bib.contains (m.group 1) do
        rep := rep.addError s!"{f}:{lineOf s m.start}: citation key [{m.group 1}] has no entry in \
          docs/references.bib"
    for m in inside.findAll s do
      rep := rep.addError s!"{f}:{lineOf s m.start}: location inside the brackets \
        ([{m.group 1}, ...]); write [{m.group 1}], ..."
    for m in thesis.findAll s do
      rep := rep.addError s!"{f}:{lineOf s m.start}: `Thesis:` tag; write \
        [QuennevilleBelair2015], ..."
    -- Python: i = s.find('/-!'); j = s.find('-/', i) (or -1); k = s.find('## References', i, j)
    let i? := findFrom s "/-!" 0
    let j? := i?.bind fun i => findFrom s "-/" i
    -- `s[i:j]` and `s.find(.., i, j)` with `j = -1` stop one character before the end
    let jEnd := match j? with | some j => j | none => s.size - 1
    let k? := i?.bind fun i => findFrom s "## References" i jEnd
    let rel := relPathFrom f "docs/references.bib"
    let decl := s!"Bibliography: [references.bib]({rel})"
    let declOk := match i? with
      | none => false
      | some i => (ofChars s i jEnd).splitOn "\n" |>.contains decl
    unless declOk do
      rep := rep.addError s!"{f}:1: module docstring lacks the line `{decl}`"
    let some k := k? | do
      rep := rep.addError s!"{f}:1: module docstring has no `## References` section"
      continue
    let mut listed : Std.HashSet String := {}
    -- `ENTRY.finditer(s, k, j)`: a negative `endpos` is clamped to `0`
    for m in entry.findAll s k (if j?.isSome then jEnd else 0) do
      let (ky, au, ti) := (m.group 3, m.group 1, m.group 2)
      listed := listed.insert ky
      if let some (bau, bti) := bib.get? ky then
        if (au, ti) != (bau, bti) then
          rep := rep.addError s!"{f}:{lineOf s m.start}: reference entry for [{ky}] should read \
            `* [{bau}, *{bti}*][{ky}]`"
    let mut seen : Std.HashSet String := {}
    for m in cite.findAll s do
      let ky := m.group 1
      if seen.contains ky then continue
      seen := seen.insert ky
      unless listed.contains ky do
        rep := rep.addError s!"{f}:{lineOf s k}: [{ky}] is cited but has no \
          `* [Author(s), *Title*][{ky}]` entry in `## References`"
  return rep.addInfo s!"CheckCitations: {files.size} files, {bib.size} bib entries, \
    {rep.errors.size} errors"

end FeecCheck.Citations
