/-
  The URI value type: the five components of RFC 3986 section 3,
  the recomposition (printing) of section 5.3, and the well formed
  predicate the round trip proof uses.

  A component that is absent is held as `none`, which is distinct
  from a component that is present and empty: a reference with no
  query and a reference with an empty query (`?` and nothing after
  it) are different values, and section 5.2 resolution treats them
  differently. The path is always present as a string; it may be
  empty.

  Every component is a list of characters, exactly as written.
  Percent escapes are neither decoded nor checked in this slice.
-/

namespace Uri

/-- A URI or URI reference, as its five components. -/
structure Uri where
  scheme : Option (List Char)
  authority : Option (List Char)
  path : List Char
  query : Option (List Char)
  fragment : Option (List Char)
deriving DecidableEq

/-- A letter, as a test. -/
def isAlpha (c : Char) : Bool :=
  decide (('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z'))

/-- A digit, as a test. -/
def isDigit (c : Char) : Bool :=
  decide ('0' ≤ c ∧ c ≤ '9')

/-- A character that may follow the first character of a scheme:
    a letter, a digit, `+`, `-`, or `.` (RFC 3986 section 3.1). -/
def isSchemeChar (c : Char) : Bool :=
  isAlpha c || isDigit c || c == '+' || c == '-' || c == '.'

/-- The scheme rule of section 3.1: a letter, then any number of
    scheme characters. -/
def schemeOk : List Char → Bool
  | [] => false
  | c :: cs => isAlpha c && cs.all isSchemeChar

/-- A component as recomposition writes it after a delimiter:
    the delimiter and the component when the component is
    present, and nothing when it is absent. -/
def withDelim (c : Char) : Option (List Char) → List Char
  | some x => c :: x
  | none => []

/-- Recomposition, as in section 5.3: the scheme and a colon when a
    scheme is present, two slashes and the authority when an
    authority is present, the path, a question mark and the query
    when a query is present, and a hash and the fragment when a
    fragment is present. -/
def print (u : Uri) : List Char :=
  (match u.scheme with
   | some s => s ++ [':']
   | none => []) ++
  (match u.authority with
   | some a => ['/', '/'] ++ a
   | none => []) ++
  u.path ++
  withDelim '?' u.query ++
  withDelim '#' u.fragment

/-- A path whose first colon, if it has one, cannot be read as the
    end of a scheme: before any colon there is either a slash or a
    run that fails the scheme rule. This is the reading Appendix B
    gives a scheme-less reference whose path is not behind an
    authority; the grammar's path-noscheme rule (no colon in the
    first segment) is the stricter form of the same condition. -/
def NoSchemePrefix (path : List Char) : Prop :=
  ∀ pre rest, path = pre ++ ':' :: rest → '/' ∈ pre ∨ schemeOk pre = false

/-- A value whose printed form splits back into the same value.
    The conditions are the ones section 5.3 and Appendix B need:

    - a present scheme follows the scheme rule;
    - a present authority holds no slash, question mark, or hash;
    - the path holds no question mark or hash;
    - with an authority, the path is empty or starts with a slash;
    - with no authority, the path does not start with two slashes;
    - a present query holds no hash;
    - with neither scheme nor authority, the path satisfies
      `NoSchemePrefix`.

    The fragment needs no condition: it is everything after the
    first hash, whatever it holds. -/
def WF (u : Uri) : Prop :=
  (∀ s, u.scheme = some s → schemeOk s = true) ∧
  (∀ a, u.authority = some a → '/' ∉ a ∧ '?' ∉ a ∧ '#' ∉ a) ∧
  ('?' ∉ u.path ∧ '#' ∉ u.path) ∧
  (∀ a, u.authority = some a → u.path = [] ∨ u.path.head? = some '/') ∧
  (u.authority = none → ¬ ∃ r, u.path = '/' :: '/' :: r) ∧
  (∀ q, u.query = some q → '#' ∉ q) ∧
  (u.scheme = none → u.authority = none → NoSchemePrefix u.path)

end Uri
