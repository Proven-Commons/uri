/-
  Path merging, dot segment removal, and reference resolution,
  following RFC 3986 section 5.2.

  A path is taken apart into a leading slash flag and its
  segments, the pieces between slashes. Empty segments, from
  consecutive slashes or a trailing slash, are segments like any
  other and are preserved.

  Dot segment removal is the segment based reading of the buffer
  algorithm of section 5.2.4. The pieces of the path are walked
  once, with the pieces kept so far held as a stack:

  - Leading `.` and `..` pieces of a relative path, each followed
    by another piece, are dropped (rule A of the RFC: the prefix
    `../` or `./` is removed). A lone leading dot piece drops
    too (rule D).
  - A `.` piece anywhere else is dropped (rule B: `/./` becomes
    `/`). A `.` piece in last place leaves a trailing slash
    behind (rule B: a trailing `/.` becomes `/`).
  - A `..` piece removes the piece kept before it (rule C). In
    last place it also leaves a trailing slash behind.
  - Any other piece is kept, with the slash that stood before it.

  The kept pieces are printed back with their slashes. When a
  `..` piece empties the stack, the next kept piece still carries
  its slash, so a relative path can come out starting with a
  slash: the RFC's algorithm replaces `/../` with `/`, and the
  slash stays. The result therefore carries its own leading
  slash flag, which the walk tracks: it turns true when a piece
  with a slash is kept while the stack is empty.

  Resolution is the strict reading of section 5.2.2: a reference
  with its own scheme is taken as it stands, apart from dot
  segment removal in its path. The non-strict reading, which
  would drop a scheme that matches the base, is not applied.
-/

import Uri.Parse

namespace Uri

/-- Add a character to the front of the first segment of a
    segment list. The empty list gains a one character segment:
    a segment list is never empty, so this is only a totality
    case. -/
def consSeg (c : Char) : List (List Char) → List (List Char)
  | [] => [[c]]
  | s :: ss => (c :: s) :: ss

/-- The segments of a path body: the pieces between slashes. The
    result is never empty; an empty body is one empty segment. -/
def splitSegs : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '/' then [] :: splitSegs cs
    else consSeg c (splitSegs cs)

/-- Join segments back with a slash between each two. -/
def joinSegs : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: ss => s ++ '/' :: joinSegs ss

/-- Take a path apart into its leading slash flag and its
    segments. -/
def splitPath (p : List Char) : Bool × List (List Char) :=
  match p with
  | '/' :: rest => (true, splitSegs rest)
  | _ => (false, splitSegs p)

/-- Print a leading slash flag and segments back into a path. -/
def printPath (lead : Bool) (segs : List (List Char)) : List Char :=
  (if lead then ['/'] else []) ++ joinSegs segs

/-- Drop the leading dot pieces of a relative path's segments,
    as rules A and D of section 5.2.4 direct: a dot piece that
    has another piece after it is dropped, and the walk repeats;
    a lone dot piece is dropped as well. -/
def stripLeadDots : List (List Char) → List (List Char)
  | [] => []
  | s :: rest =>
    if (s = ['.'] ∨ s = ['.', '.']) then
      if rest = [] then [] else stripLeadDots rest
    else s :: rest

/-- The last piece of a path, in the dot segment walk. `out` is
    the stack of kept segments, most recent first; `abs` is the
    leading slash flag the result will carry. A dot piece in
    last place with a slash before it leaves a trailing empty
    segment, and a `..` piece first removes the segment kept
    before it. A dot piece with no slash before it, which can
    only stand alone, is dropped. -/
def lastPiece (out : List (List Char)) (abs : Bool) (b : Bool)
    (s : List Char) : Bool × List (List Char) :=
  if s = ['.'] ∨ s = ['.', '.'] then
    if b then
      let out' := if s = ['.', '.'] then out.drop 1 else out
      (if out' = [] then true else abs, out'.reverse ++ [[]])
    else (abs, out.reverse)
  else (abs ∨ (b ∧ out.isEmpty), out.reverse ++ [s])

/-- The dot segment walk over path pieces. Each piece is a slash
    flag and a segment. `.` pieces drop, `..` pieces remove the
    segment kept before them, and every other piece is kept. A
    piece kept while the stack is empty sets the result's
    leading slash flag from its own slash. The result is the
    flag and the kept segments, in order. -/
def foldRds (out : List (List Char)) (abs : Bool) :
    List (Bool × List Char) → Bool × List (List Char)
  | [] => (abs, out.reverse)
  | (b, s) :: rest =>
    match rest with
    | [] => lastPiece out abs b s
    | _ :: _ =>
      if s = ['.'] then foldRds out abs rest
      else if s = ['.', '.'] then foldRds (out.drop 1) abs rest
      else foldRds (s :: out) (abs ∨ (b ∧ out.isEmpty)) rest

/-- Dot segment removal on a path taken apart as a leading slash
    flag and segments: strip the leading dot pieces of a
    relative path, walk the pieces, and return the flag and
    segments of the result. -/
def rdsSegs (lead : Bool) (segs : List (List Char)) :
    Bool × List (List Char) :=
  let segs' := if lead then segs else stripLeadDots segs
  match segs' with
  | [] => (lead, [])
  | s :: ss =>
    foldRds [] lead ((lead, s) :: ss.map (fun x => (true, x)))

/-- Remove dot segments from a path, as section 5.2.4 directs. -/
def removeDotSegments (p : List Char) : List Char :=
  let (lead, segs) := splitPath p
  let (lead', segs') := rdsSegs lead segs
  printPath lead' segs'

/-- A path up to and including its last slash, or empty when it
    has no slash. -/
def upToLastSlash : List Char → List Char
  | [] => []
  | c :: cs =>
    if cs.contains '/' then c :: upToLastSlash cs
    else if c = '/' then ['/']
    else []

/-- Merge a relative reference path with a base path, as section
    5.2.3 directs: when the base has an authority and an empty
    path, the merged path is a slash and the reference path;
    otherwise it is the base path up to and including its last
    slash, then the reference path. -/
def mergePaths (baseHasAuth : Bool) (basePath refPath : List Char) :
    List Char :=
  if baseHasAuth ∧ basePath = [] then '/' :: refPath
  else upToLastSlash basePath ++ refPath

/-- The path of a resolution whose reference has neither scheme
    nor authority: the base path when the reference path is
    empty, the dot-removed reference path when it is absolute,
    and the dot-removed merge otherwise. -/
def resolvedPath (base ref : Uri) : List Char :=
  if ref.path = [] then base.path
  else if ref.path.head? = some '/' then removeDotSegments ref.path
  else removeDotSegments
    (mergePaths base.authority.isSome base.path ref.path)

/-- Resolve a reference against a base, by the strict transform
    of section 5.2.2. The fragment always comes from the
    reference. A reference with a scheme is taken as it stands,
    apart from dot segment removal in its path. -/
def resolve (base ref : Uri) : Uri :=
  if ref.scheme.isSome then
    { ref with path := removeDotSegments ref.path }
  else if ref.authority.isSome then
    ⟨base.scheme, ref.authority, removeDotSegments ref.path,
     ref.query, ref.fragment⟩
  else
    ⟨base.scheme, base.authority, resolvedPath base ref,
     (match ref.path, ref.query with
      | [], none => base.query
      | _, q => q),
     ref.fragment⟩

end Uri
