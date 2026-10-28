/-
  Command line front end, used by the tests.

  Reads one request per line and prints one answer per line. A
  request is an operation, then one space and its input fields.
  The fields of a request are separated by the semicolon
  character itself, and each field is a string written as
  comma-separated decimal character codes.

    split 102,111,111,58,47,47,97,47,98
      prints  ok:102,111,111;97;47,98;;
    resolve 104,116,116,112,58,47,47,97,47,98;103
      prints  ok:104,116,116,112,58,47,47,97,47,103

  The `split` operation takes one field: a URI reference. Its
  answer is `ok:` and the five components of the split, as
  fields in the same form, in the order scheme, authority,
  path, query, fragment. An empty field stands for an absent
  component; the path field holds the path's codes, which may
  be none. A present component with no characters gives an
  empty field too, so an absent component and a present empty
  one cannot be told apart in a split answer. The values keep
  them apart, and so does resolution: the reference `?` brings
  an empty query where the empty reference brings none.
  Splitting never fails.

  The `resolve` operation takes two fields: a base and a
  reference. Its answer is `ok:` and the character codes of
  the resolved reference, recomposed as section 5.3 directs.
  Resolution never fails either.

  A request may also be the operation alone, with no space and
  no fields; that is the operation on the empty string, or a
  malformed request for `resolve`, which needs its two fields.
  A malformed request prints `error`: any other line, an
  unknown operation, the wrong number of fields, a number that
  is not plain decimal digits, or a character code that is not
  a Unicode scalar value. A line may end in LF or CR LF;
  nothing else around a request is ignored.

  The work here calls `Uri.split`, `Uri.resolve`, and
  `Uri.print` directly. The line handling is covered by the
  tests, not by a proof.
-/

import Uri

open Uri

/-- A number in plain decimal digits. Longer numbers than any
    character code are refused before they are converted, since
    that takes time quadratic in their length. -/
def number (t : String) : Option Nat :=
  let ds := t.toList
  if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
  else t.toNat?

/-- The comma-separated numbers in `s`. -/
def numbers (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM number

/-- The numbers as characters. A number that is not a Unicode
    scalar value makes the request malformed. -/
def toChars (ns : List Nat) : Option (List Char) :=
  ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none

def showCodes (cs : List Char) : String :=
  ",".intercalate (cs.map fun c => toString c.toNat)

/-- A component as an answer field: its codes, or the empty
    field when the component is absent. -/
def showOpt (o : Option (List Char)) : String :=
  match o with
  | some cs => showCodes cs
  | none => ""

/-- The answer to one request, or `none` when the request is
    malformed. -/
def answer (op : String) (arg : String) : Option String :=
  match op with
  | "split" =>
    match numbers arg >>= toChars with
    | none => none
    | some cs =>
      let u := split cs
      some ("ok:" ++ ";".intercalate
        [showOpt u.scheme, showOpt u.authority, showCodes u.path,
         showOpt u.query, showOpt u.fragment])
  | "resolve" =>
    match arg.splitOn ";" with
    | [b, r] =>
      match numbers b >>= toChars, numbers r >>= toChars with
      | some bs, some rs =>
        some ("ok:" ++ showCodes (print (resolve (split bs) (split rs))))
      | _, _ => none
    | _ => none
  | _ => none

/-- The answer to one line: an operation, then optionally one
    space and its fields. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | [op] => answer op ""
  | [op, arg] => answer op arg
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := chomp line
    stdout.putStrLn ((request line).getD "error")
