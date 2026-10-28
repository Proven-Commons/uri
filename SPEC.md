# Specification: uri

A URI reference split and resolver in Lean, following
RFC 3986: the decomposition of section 3 and Appendix B,
recomposition as in section 5.3, and reference resolution as
in section 5.2. Percent escapes are left exactly as written,
as section 5.2 directs. Normalization, as in section 6, is a
later slice.

This slice does not check the grammar of section 3. A string
that is not a legal URI reference may still split here, and
its components may hold characters the grammar would forbid
in them. The one piece of grammar the split uses is the
scheme rule, because the reading of Appendix B needs it to
tell a scheme from a path. A full grammar check is the
second slice. The spelling of percent escapes, the forms of
hosts and ports, and whether a scheme is registered are not
checked either.

## The value

A URI or URI reference is held as its five components: a
scheme, an authority, a path, a query, and a fragment. Each
component is a list of characters, exactly as written.

The scheme, authority, query, and fragment may be absent.
An absent component is distinct from a component that is
present and empty: a reference ending in `?` has an empty
query, a reference with no `?` has none, and section 5.2
treats the two differently. The path is always present as a
string; it may be empty.

## The split

The split takes a reference apart in this order, the order
Appendix B describes:

1. The fragment is everything after the first `#`. What
   stands before it goes on.
2. The query is everything after the first `?` in what
   remains. What stands before it goes on.
3. A scheme is found when the run before the first colon
   follows the scheme rule of section 3.1: a letter, then
   any number of letters, digits, `+`, `-`, or `.`. The
   scheme is that run, and what follows the colon goes on.
   A colon that comes after a slash cannot end a scheme:
   the run before it holds the slash and fails the rule.
4. An authority is present when what remains starts with
   `//`. It runs to the next slash, or to the end.
5. The rest is the path.

No other character is checked at any step.

## Recomposition

Printing a value follows section 5.3: the scheme and a
colon when a scheme is present, two slashes and the
authority when an authority is present, the path, a question
mark and the query when a query is present, and a hash and
the fragment when a fragment is present. Nothing else is
added or taken away.

## Merge

Merging a base path with a relative reference path follows
section 5.2.3: when the base has an authority and an empty
path, the merged path is a slash and the reference path.
Otherwise it is the base path up to and including its last
slash, then the reference path. A base path with no slash
contributes nothing.

## Dot segment removal

Removing dot segments from a path follows section 5.2.4.
The reading here works on the segments of the path, the
pieces between slashes, which the statement of the algorithm
in the RFC also speaks of. Empty segments, from consecutive
slashes or a trailing slash, are segments like any other and
are preserved.

1. The path is taken apart into a leading slash flag and
   its segments.
2. Leading `.` and `..` segments of a relative path are
   dropped, one after another, as rules A and D of the RFC
   direct.
3. The remaining pieces are walked once, with the pieces
   kept so far held as a stack. A `.` piece is dropped. A
   `..` piece drops itself and removes the piece kept
   before it, if there is one. Any other piece is kept,
   with the slash that stood before it.
4. A `.` or `..` piece in last place, with a slash before
   it, leaves a trailing empty segment behind: a trailing
   `/.` or `/..` becomes a trailing slash. A lone dot piece
   with no slash before it is dropped and leaves nothing.

The kept pieces are printed back with their slashes. When a
`..` piece empties the stack, the next kept piece still
carries its slash, because the RFC's algorithm replaces
`/../` with `/` and the slash stays. So a relative path can
come out of removal starting with a slash: removing dot
segments from `a/../b` gives `/b`.

The two worked examples of the RFC: `/a/b/c/./../../g`
becomes `/a/g`, and `mid/content=5/../6` becomes `mid/6`.

## Resolution

Resolution is the strict transform of section 5.2.2. The
fragment always comes from the reference. Then:

- The reference has a scheme: the target is the reference
  as it stands, apart from dot segment removal in its path.
  The non-strict reading, which would drop a scheme that
  matches the base, is not applied: against the base
  `http://a/b/c/d;p?q`, the reference `http:g` resolves to
  `http:g`.
- Otherwise, the reference has an authority: the target
  takes the base scheme, the reference authority, the
  reference path with dot segments removed, and the
  reference query.
- Otherwise, the reference path is empty: the target path
  is the base path, and the target query is the reference
  query when it is present, even empty, and the base query
  otherwise.
- Otherwise, the reference path starts with a slash: it is
  the target path, with dot segments removed.
- Otherwise: the target path is the merge of the base path
  and the reference path, with dot segments removed.

In the last three shapes the target takes the base scheme
and the base authority as well.

Dot segments in a query or a fragment are not processed:
they are not part of the path. The worked examples of
sections 5.4.1 and 5.4.2, under the strict reading, are the
fixed cases of the test suite.

## Well formed values

Splitting a printed value gives the value back when the
value is well formed, in this sense:

- a present scheme follows the scheme rule;
- a present authority holds no slash, question mark, or
  hash;
- the path holds no question mark or hash;
- with an authority, the path is empty or starts with a
  slash;
- with no authority, the path does not start with two
  slashes;
- a present query holds no hash;
- with neither scheme nor authority, the path has no scheme
  prefix: before any colon there is either a slash or a run
  that fails the scheme rule.

The fragment needs no condition: it is everything after the
first hash, whatever it holds. Without these conditions a
printed value can be genuinely ambiguous. A path of `a:b`
printed with no scheme reads back as the scheme `a` and the
path `b`.

## The command line protocol

The tool in `Main.lean` reads one request per line and
prints one answer per line. A request is an operation, then
one space and its input fields. The fields of a request are
separated by the semicolon character itself, and each field
is a string written as comma-separated decimal character
codes. Character codes are Unicode scalar values.

- `split` takes one field, a URI reference. Its answer is
  `ok:` and the five components of the split as fields in
  the same form, in the order scheme, authority, path,
  query, fragment. Splitting never fails.
- `resolve` takes two fields, a base and a reference. Its
  answer is `ok:` and the character codes of the resolved
  reference, recomposed as above. Resolution never fails.

A request may also be the operation alone, with no space and
no fields: the operation on the empty string, or a malformed
request for `resolve`, which needs its two fields.

A split answer writes an absent component as an empty field.
A present component with no characters gives an empty field
too, so the two cannot be told apart in a split answer. The
values keep them apart, and so does resolution, as the
resolution section describes.

A malformed request prints `error`: any other line, an
unknown operation, the wrong number of fields, a number that
is not plain decimal digits, or a character code that is not
a Unicode scalar value. A line may end in LF or CR LF;
nothing else around a request is ignored.
