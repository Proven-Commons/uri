/-
  The split: decompose a reference into its five components,
  following the structure of RFC 3986 section 3 and Appendix B.

  The order of the steps is the one Appendix B describes. The
  fragment is everything after the first `#`. The query is
  everything after the first `?` in what remains. A scheme is a
  leading run that matches the scheme rule and ends at the first
  `:`; a colon that comes after a slash fails the scheme rule on
  its own, because `/` is not a scheme character. An authority is
  present when what remains starts with `//`, and it runs to the
  next slash. The rest is the path.

  No other character is checked. A full grammar check is the
  second slice: a string that is not a legal URI reference may
  still split here, and its components may hold characters the
  section 3 grammar would forbid in them.
-/

import Uri.Value

namespace Uri

/-- Split a list at its first occurrence of `c`: the part before
    it, and `some` of the part after it, or `none` when `c` does
    not occur. -/
def splitFirst (c : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | x :: xs =>
    if x = c then ([], some xs)
    else
      let r := splitFirst c xs
      (x :: r.1, r.2)

/-- Split a list at its first occurrence of `c`, keeping the
    delimiter with the second part: the run before `c`, and the
    rest starting at `c`, or the whole list at the end when `c`
    does not occur. -/
def takeUntil (c : Char) : List Char → List Char × List Char
  | [] => ([], [])
  | x :: xs =>
    if x = c then ([], x :: xs)
    else
      let r := takeUntil c xs
      (x :: r.1, r.2)

/-- The scheme at the head of a string, if there is one: the run
    before the first colon, when that run matches the scheme rule,
    together with what follows the colon. -/
def schemeOf (s : List Char) : Option (List Char × List Char) :=
  match splitFirst ':' s with
  | (pre, some rest) => if schemeOk pre then some (pre, rest) else none
  | _ => none

/-- The scheme step of the split: when `schemeOf` finds a
    scheme, the scheme and what follows its colon; otherwise no
    scheme, and the whole string goes on to the next step. -/
def splitScheme (t : List Char) : Option (List Char) × List Char :=
  match schemeOf t with
  | some (sch, r) => (some sch, r)
  | none => (none, t)

/-- The authority step of the split: when the first two
    characters are two slashes, the authority is the run up to
    the next slash and the rest is the path; otherwise there is
    no authority and the whole string is the path. -/
def splitAuthority (t : List Char) : Option (List Char) × List Char :=
  if t.take 2 = ['/', '/'] then
    let (a, p) := takeUntil '/' (t.drop 2)
    (some a, p)
  else (none, t)

/-- Split a reference into its five components. -/
def split (s : List Char) : Uri :=
  let (noFrag, frag) := splitFirst '#' s
  let (noQuery, query) := splitFirst '?' noFrag
  let (scheme, rest) := splitScheme noQuery
  let (auth, path) := splitAuthority rest
  ⟨scheme, auth, path, query, frag⟩

end Uri
